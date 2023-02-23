use std::fs;
use std::path::Path;
use std::str::{Split, from_utf8};
use std::vec;
use std::iter;
use std::collections::HashMap;

extern crate ahash;
use ahash::AHashMap;

enum TKind {
    IntLit, FloatLit, Ident, WSpace, StrLit, Punc, Op, PrefOp, Null
}

enum NKind {
    IntLit, FloatLit, Ident, Call, StrLit, Rt
}

pub fn main() {
    let prec_txt = fs::read_to_string(Path::new("../resources/precedence.txt")).unwrap();
    let prec_lines = prec_txt.split('\n').filter(|x| *x != "").collect::<Vec<&str>>();

    let sym_txt = fs::read_to_string(Path::new("../resources/symbols.txt")).unwrap();
    let syms = sym_txt.split('\n').collect::<Vec<&str>>();

    
    let whitespaces : Vec<char> = syms[2].split(',').map(|x| (*x).chars().nth(0).unwrap()).collect();
    let punc : Vec<char> = syms[0].split(',').map(|x| (*x).chars().nth(0).unwrap()).collect();
    let end_word : Vec<char> = whitespaces.iter().map(|x| *x).chain([',']).collect();
    let pref_ops : Vec<char> = syms[4].split(',').map(|x| (*x).chars().nth(0).unwrap()).collect();
    let ops : Vec<char> = prec_txt.split(['\n', ',']).filter(|x| x.len()  > 0).map(|x| x.chars().nth(0).unwrap()).collect();

    println!("{:?}", whitespaces);
    
    let precs : AHashMap<char, u32> = {
        let mut precs : AHashMap<char, u32> = AHashMap::new();
        for i in 0..prec_lines.len() {
            for o in prec_lines[i].chars() {
                if o != ',' {
                    precs.insert(o, (prec_lines.len() - i) as u32);
                }
            }
        }
        precs
    };

    let lex_stop : Vec<char> = ops.iter().map(|x| *x)
        .chain(pref_ops.iter().map(|x| *x))
        .chain(syms[1]
               .split(',')
               .filter(|x| x.len() > 0)
               .map(|x| (*x).chars().nth(0).unwrap()))
        .chain([',', '\n']).collect();
    
    println!("{:?}", partFile(&String::from(syms[6]), &lex_stop));
}

fn partFile(inp : &String, lex_stop : &Vec<char>) -> Vec<String> {
    let mut result : Vec<String> = Vec::new();
    let mut c_word : String = String::from("");
    for c in inp.chars() {
        if lex_stop.iter().any(|x| *x == c) {
            if c_word.len() != 0 {
                result.push(c_word);
            }
            result.push(String::from(c));
            c_word = String::from("");
        } else {
            c_word.push(c);
        }
    }
    if c_word.len() > 0 && lex_stop.iter().any(|x| *x == c_word.chars().nth(0).unwrap()) {
        result.push(c_word);
    }
    return result;
}
