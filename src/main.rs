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

// use std::io::Read;
// use std::mem::size_of;

use std::io::stdout;
use std::io::Write;
fn main() -> Result<(), std::io::Error> {
    let port = open()?;

    let mut buffer = [0; 256];
    // loop {
    //     if let Ok(read) = port.read(&mut buffer) {
    //         if let Ok(s) = std::str::from_utf8(&buffer[0..read]) {
    //             print!("{}", s);
    //         }
    //     }
    // }

    loop {
        match port.read(&mut buffer) {
            Ok(0) => print!("[0]"),
            Ok(n) => {
                for i in &buffer[0..n] {
                    print!("{:#03x} ", *i);
                }
                let _ = stdout().flush();

                // if let Ok(s) = std::str::from_utf8(&buffer[0..n]) {
                //     println!("{}", s);
                // }
            }
            Err(ref e) if e.kind() == std::io::ErrorKind::TimedOut => continue,
            Err(e) => {
                eprintln!("Error: Failed to read ");
            }
        }
    }
    Ok(())
}
