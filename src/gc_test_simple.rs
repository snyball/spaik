use risp::nkgc::Arena;

fn main() {
    let mut ar = Arena::new(1024);
    let num = 100000;
    for _ in 0..num {
        ar.push_new(String::from("BURN BABY BURN"));
        ar.pop().unwrap();
    }
}
