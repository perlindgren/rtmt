use rtmt::short_frame_decode::NcDecode;
use serial2::SerialPort;
use std::time::Duration;
// On Windows, use something like "COM1".
// For COM ports above COM9, you need to use the win32 device namespace, for example "\\.\COM10" (or "\\\\.\\COM10" with string escaping).
// For more details, see: https://learn.microsoft.com/en-us/windows/win32/fileio/naming-a-file?redirectedfrom=MSDN#win32-device-namespaces

#[cfg(target_os = "linux")]
static COM_PATH: &str = "/dev/ttyUSB1";
#[cfg(target_os = "windows")]
static COM_PATH: &str = "COM3";

// A one second timeout
const TIME_OUT: Duration = Duration::from_millis(1000);

pub fn open() -> std::io::Result<SerialPort> {
    let mut port = SerialPort::open(COM_PATH, 115200)?;
    // Needed for windows, but should not hurt on Linux
    port.set_dtr(true)?;
    port.set_rts(true)?;
    port.set_write_timeout(TIME_OUT)?;
    port.set_read_timeout(TIME_OUT)?;

    Ok(port)
}

use std::io::stdout;
use std::io::Write;
fn main() -> Result<(), std::io::Error> {
    let port = open()?;

    let mut buffer = [0; 256];
    let mut de = NcDecode::new();

    loop {
        match port.read(&mut buffer) {
            Ok(0) => panic!("[0]"),
            Ok(n) => {
                for b in &buffer[0..n] {
                    print!("{:#03x} ", *b);
                    if let Some(frame_start) = de.decode(*b as i8) {
                        let s: Vec<u8> = de.out_buf.iter().map(|i| *i as u8).collect();
                        println!("---- str {:?}", std::str::from_utf8(&s));
                        if frame_start == -1 {
                            // clear both receive buffer and output buffer
                            // when outermost frame received
                            de.clear_out();
                            de.clear_in();
                        }
                    }
                }
                let _ = stdout().flush();
            }
            Err(ref e) if e.kind() == std::io::ErrorKind::TimedOut => continue,
            Err(_e) => {
                eprintln!("Error: Failed to read ");
            }
        }
    }
}
