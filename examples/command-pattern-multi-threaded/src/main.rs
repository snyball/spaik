use serde::Deserialize;
use spaik::prelude::*;
use spaik::EnumCall;

#[derive(Debug, Deserialize, Clone, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
enum Msg {
    Test { id: i32 },
}

#[derive(Debug, Deserialize, Clone, PartialEq, Eq, EnumCall)]
#[serde(rename_all = "kebab-case")]
enum Cmd {
    Add(i32),
    Subtract(i32)
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut vm = Spaik::new();
    vm.add_load_path(".");
    vm.load("async-example")?;
    let mut vm = vm.fork::<Msg, Cmd>();

    vm.cmd(Cmd::Add(10));
    vm.cmd(Cmd::Add(20));

    // Loop until all commands have been responded to
    let mut recvd = 0;
    while recvd < 2 {
        while let Some(p) = vm.recv() {
            assert_eq!(p.get(), &Msg::Test { id: 1337 });
            vm.fulfil(p, 31337);
            recvd += 1;
        }
    }

    // We can join with the VM again on the same thread
    let mut vm = vm.join();
    let glob: i32 = vm.eval("*global*").unwrap();
    assert_eq!(glob, 10 + 31337 + 1 + 20 + 31337 + 1);

    Ok(())
}
