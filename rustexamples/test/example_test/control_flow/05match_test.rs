enum Coin {
    Penny,
    Nickel,
    Dime,
    Quarter,
}

fn value_in_cents(coin: Coin) -> u8 {
    match coin with {
        case Coin::Penny as c => {
			return 1;
		}
		case Coin::Nickel as c => {
			return 5;
		}
		case Coin::Dime as c => {
			return 10;
		}
		case Coin::Quarter as c => {
			return 25;
		}
    }
}



fn main() {
	let x : u8 = value_in_cents(Coin::Quarter);
}




