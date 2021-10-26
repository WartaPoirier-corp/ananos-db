use clap::{App, Arg};
use adb::{DbObject, DbValue};
use std::sync::Arc;

fn main() {
    let matches = App::new("adb-write-date")
        .version("0.1.0")
        .author("Ana Gelez <ana@gelez.xyz>")
        .about("Writes a date in an ananOS database")
        .arg(Arg::with_name("FILE")
            .help("The database to display"))
        .arg(Arg::with_name("type")
             .help("Only display items of this type (Type ID, or full name)")
             .takes_value(true)
             .short("t")
             .long("type"))
        .arg(Arg::with_name("year").help("The year"))
        .arg(Arg::with_name("month").help("The month"))
        .arg(Arg::with_name("day").help("The day"))
        .get_matches();

    let file = std::fs::OpenOptions::new()
        .read(true)
        .write(true)
        .open(matches.value_of("FILE").unwrap()).unwrap();
    let mut db = adb::Db::read_from(file).unwrap();
    let date = DbObject {
        type_info: db.get_type_info(adb::TypeId(0x00DA)).expect("Date type is not present, this program cannot insert it yet"),
        value: Arc::new(DbValue::Product {
            fields: vec![
                Arc::new(DbValue::U64(matches.value_of("year").expect("Please provide a year").parse().unwrap())),
                Arc::new(DbValue::U64(matches.value_of("month").expect("Please provide a month").parse().unwrap())),
                Arc::new(DbValue::U64(matches.value_of("day").expect("Please provide a day").parse().unwrap())),
            ]
        })
    };
    db.write_object(date).unwrap();
}

