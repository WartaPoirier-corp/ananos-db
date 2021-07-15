use clap::{Arg, App};
use prettytable::*;

fn main() {
    let matches = App::new("adb-show")
        .version("0.1.0")
        .author("Ana Gelez <ana@gelez.xyz>")
        .about("Displays the contents of an ananOS database")
        .arg(Arg::with_name("FILE")
            .help("The database to display"))
        .arg(Arg::with_name("type")
             .help("Only display items of this type (Type ID, or full name)")
             .takes_value(true)
             .short("t")
             .long("type"))
        .get_matches();

    let file = std::fs::File::open(matches.value_of("FILE").unwrap()).unwrap();
    let mut ty_filter = matches.value_of("type");
    let ty_id_filter: Option<u64> = ty_filter.clone()
        .and_then(|x|
            x.parse().ok()
                .or_else(|| u64::from_str_radix(x, 16).ok())
        );
    if ty_id_filter.is_some() {
        ty_filter = None; 
    }
    
    println!();

    let mut db = adb::Db::read_from(file).unwrap();
    'types: for ty in db.all_type_ids() {
        if let Some(filter) = ty_id_filter {
            if filter != ty.0 {
                continue;
            }
        }

        let mut table = Table::new();
        table.set_format(style());
        let mut headers = false;
        for obj in db.iter_type(ty) {
            if !headers {
                if let Some(filter) = ty_filter {
                    if filter != obj.type_info.name {
                        continue 'types;                    
                    }
                }

                print!("——— TYPE 0x{:04X} — ", ty.0);
                println!("\x1b[1m{}\x1b[0m ———\n", obj.type_info.name);

                match obj.type_info.definition {
                    adb::TypeDef::U64 => {
                        table.add_row(row![b -> "Value"]);
                    },
                    adb::TypeDef::Product { ref fields } => {
                        table.add_row(Row::new(fields.iter().map(|f|
                            Cell::new(&f.0)
                                .with_style(Attr::Bold)).collect())
                        );
                    },
                    _ => {},
                }
                headers = true;
            }

            match show(&obj) {
                TableElem::Cell(s) => table.add_row(row!(s)),
                TableElem::Row(r) => table.add_row(r),
            };
        }
        table.printstd();
        println!()
    }
}

enum TableElem {
    Cell(String),
    Row(Row),
}

fn show(obj: &adb::DbObject) -> TableElem {
    // dbg!(&obj.value);
    match *obj.value {
        adb::DbValue::U64(x) => TableElem::Cell(x.to_string()),
        adb::DbValue::Product { ref fields } => {
            TableElem::Row(Row::new(fields.iter()
                .map(|f| match show(f) {
                    TableElem::Cell(s) => cell!(s),
                    TableElem::Row(r) => {
                        let mut t = Table::init(vec![r]);
                        t.set_format(style());
                        cell!(t)
                    },
                })
                .collect()))
        },
        adb::DbValue::Sum { variant, ref data } => {
            let variant_name = match obj.type_info.definition {
                adb::TypeDef::Sum { ref variants } => variants[variant as usize].0.clone(),
                _ => {
                    println!("Warning: type and value are inconsistent");
                    variant.to_string()
                }
            };
            TableElem::Row(row!(variant_name, match show(data) {
                TableElem::Cell(c) => cell!(c),
                TableElem::Row(r) => {
                    let mut t = Table::init(vec![r]);
                    t.set_format(style());
                    cell!(t)
                },
            }))
        },
        adb::DbValue::Array(ref items) => {
            let items = items.iter();
            if let Some(first) = items.clone().next() {
                // TODO: real check for a string
                let string = if first.type_info.id == adb::type_ids::U8 {
                    String::from_utf8(items.clone().map(|i| match *i.value {
                        adb::DbValue::U64(b) => b as u8,
                        _ => panic!("This was not a string"),
                    }).collect()).ok()
                } else {
                    None
                };

                if let Some(string) = string {
                    TableElem::Cell(string)
                } else {
                    let mut inline = true;
                    let content = items.map(|i| match show(i) {
                        TableElem::Cell(c) => c,
                        TableElem::Row(r) => {
                            inline = false;
                            let mut t = Table::init(vec![r]);
                            t.set_format(style());
                            t.to_string()
                        },
                    }).collect::<Vec<_>>();

                    if inline {
                        TableElem::Cell(format!("[ {} ]", content.join(", ")))
                    } else {
                        TableElem::Cell(format!("{}", content.join("")))
                    }

                }
            } else {
                TableElem::Cell(String::new())
            }
        },
        _ => todo!(),
    }
}

fn style() -> format::TableFormat {
    format::FormatBuilder::new()
        .column_separator('│')
        .borders('│')
        .separators(&[
                    format::LinePosition::Title, format::LinePosition::Intern],
                    format::LineSeparator::new('─', '┼', '├', '┤'))
        .separators(&[format::LinePosition::Top],
                    format::LineSeparator::new('─', '┬', '┌', '┐'))
        .separators(&[format::LinePosition::Bottom],
                    format::LineSeparator::new('─', '┴', '└', '┘'))
        .padding(1, 1)
        .build()
}
