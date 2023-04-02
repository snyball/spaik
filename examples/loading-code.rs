use spaik::Spaik;

pub fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut vm = Spaik::new();

    // We need to specify a load-path first
    vm.add_load_path("examples");

    vm.load("to-be-loaded")?;

    Ok(())
}
