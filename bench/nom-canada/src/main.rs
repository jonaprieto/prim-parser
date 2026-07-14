use nom::{branch::alt, bytes::complete::{take_while, take_while1}, character::complete::char, multi::separated_list0, IResult};
use std::fs;
fn ws(i: &[u8]) -> IResult<&[u8], ()> { let (i,_) = take_while(|c| c==b' '||c==b'\n'||c==b'\r'||c==b'\t')(i)?; Ok((i,())) }
fn num(i: &[u8]) -> IResult<&[u8], usize> { let (i,_) = take_while1(|c:u8| c.is_ascii_digit()||c==b'-'||c==b'+'||c==b'.'||c==b'e'||c==b'E')(i)?; Ok((i,1)) }
fn string(i: &[u8]) -> IResult<&[u8], usize> { let (i,_) = char('"')(i)?; let (i,_) = take_while(|c| c!=b'"')(i)?; let (i,_) = char('"')(i)?; Ok((i,1)) }
fn keyword(i: &[u8]) -> IResult<&[u8], usize> { let (i,_) = take_while1(|c:u8| c.is_ascii_lowercase())(i)?; Ok((i,1)) }
fn array(i: &[u8]) -> IResult<&[u8], usize> { let (i,_) = char('[')(i)?; let (i,xs) = separated_list0(char(','), value)(i)?; let (i,_) = ws(i)?; let (i,_) = char(']')(i)?; Ok((i, 1+xs.iter().sum::<usize>())) }
fn pair(i: &[u8]) -> IResult<&[u8], usize> { let (i,_) = ws(i)?; let (i,_) = char('"')(i)?; let (i,_) = take_while(|c| c!=b'"')(i)?; let (i,_) = char('"')(i)?; let (i,_) = ws(i)?; let (i,_) = char(':')(i)?; value(i) }
fn object(i: &[u8]) -> IResult<&[u8], usize> { let (i,_) = char('{')(i)?; let (i,xs) = separated_list0(char(','), pair)(i)?; let (i,_) = ws(i)?; let (i,_) = char('}')(i)?; Ok((i, 1+xs.iter().sum::<usize>())) }
fn value(i: &[u8]) -> IResult<&[u8], usize> { let (i,_) = ws(i)?; alt((num, string, array, object, keyword))(i) }
fn main() {
    let bs = fs::read("bench-data/canada.json").unwrap();
    if std::env::args().any(|a| a == "time") {
        let mut best = f64::INFINITY; let mut acc = 0usize;
        for _ in 0..100 { let t = std::time::Instant::now(); let (_, n) = value(&bs).unwrap(); let e = t.elapsed().as_secs_f64()*1000.0; acc = acc.wrapping_add(n); if e < best { best = e; } }
        println!("count={} parse_ms={:.3}", acc/100, best); std::hint::black_box(acc);
    } else { println!("{}", value(&bs).unwrap().1); }
}
