pub mod cfg;
pub mod graph;
pub mod restructure;

#[cfg(test)]
mod test {
    use std::{
        io::Write,
        process::{Command, Stdio},
    };

    pub fn bril2json(src: &str) -> String {
        let mut child = Command::new("bril2json")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .unwrap();
        let mut stdin = child.stdin.take().unwrap();
        stdin.write_all(src.as_bytes()).unwrap();
        drop(stdin);

        String::from_utf8(child.wait_with_output().unwrap().stdout).unwrap()
    }

    pub fn brili(src: &str) -> (String, usize) {
        let mut child = Command::new("brili")
            .arg("-p")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        let mut stdin = child.stdin.take().unwrap();
        stdin.write_all(src.as_bytes()).unwrap();
        drop(stdin);

        let result = child.wait_with_output().unwrap();
        let stdout = String::from_utf8(result.stdout).unwrap();
        let stderr = String::from_utf8(result.stderr).unwrap();

        (
            stdout,
            stderr
                .trim_start_matches("total_dyn_inst: ")
                .trim()
                .parse()
                .unwrap_or(114514),
        )
    }
}
