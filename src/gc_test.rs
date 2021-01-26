use spaik::nkgc::*;
use spaik::parse::parse;
use std::time::SystemTime;

pub fn fuck(ar: &mut Arena) {
    ar.push_new(String::from("FUCK"));
    ar.push_new(String::from("FUCK FUCK"));
    ar.push_new(String::from("FUCK FUCK FUCK"));
    ar.push_new(String::from("FUCK FUCK FUCK FUCK"));
    ar.push_new(String::from("FUCK FUCK FUCK FUCK FUCK"));
    ar.push_new(String::from("YEEEEEEEEEEEEE BOIIIIIII"));
    ar.list(6);
}

fn print_stats(start_time: SystemTime, ar: &Arena) {
    println!("{},{}",
             SystemTime::now().duration_since(start_time).unwrap().as_micros(),
             ar.stats().usage);
}

pub fn main() {
    let num = 500;
    let mut ar = Arena::new(8192 * 2);
    let start_time = SystemTime::now();
    fuck(&mut ar);
    ar.pop().unwrap();
    fuck(&mut ar);
    let v = parse("(defun (x y z) (println (cos (+ (/ x y) z))) (println \"test\"))").unwrap();
    for i in 0..num {
        fuck(&mut ar);
        ar.push_new(String::from("FUCK"));
        ar.pop().unwrap();
        ar.pop().unwrap();
        ar.push_ast(&*v);
        if i % 5 != 0 {
            ar.pop().unwrap();
        }
        ar.collect();
        print_stats(start_time, &ar);
    }
    while ar.pop().is_ok() {
        ar.collect();
        fuck(&mut ar);
        ar.push_ast(&*v);
        ar.pop().unwrap();
        ar.pop().unwrap();
        print_stats(start_time, &ar);
    }
    ar.full_collection();
    print_stats(start_time, &ar);
}
