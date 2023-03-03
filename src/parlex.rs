use std::fs;
use std::path::Path;
use std::fmt::{Debug, Formatter, Error};
use std::write;

extern crate ahash;
use ahash::AHashMap;


struct ParseDat {
    whitespaces : Vec<char>,
    punc : Vec<char>,
    pref_ops : Vec<char>,
    ops : Vec<char>
}







#[derive(Debug)]
#[allow(dead_code)]
enum TKind {
    IntLit, FloatLit, Ident, WSpace, StrLit, Punc, Op, PrefOp, Null
}


#[derive(Debug)]
enum HvNum {
    Int(i32), Float(f32)
}

#[derive(Debug)]
#[allow(dead_code)]
enum NKind {
    IntLit(HvNum), FloatLit(HvNum), Ident(String), Call(String), StrLit(String), Rt
}

struct Token {
    kind : TKind,
    val : String
}

impl Debug for Token {
    fn fmt(&self, f : &mut Formatter<'_>) -> Result<(), Error> {
        return write!(f, "{:?} {}", self.kind, self.val)
    }
}



struct ASTNode {
    kind : NKind,
    kids : Option<Vec<ASTNode>>
}
    
impl ASTNode {
    pub fn new() -> Self {
        return ASTNode {kind : NKind::Rt, kids : None};
    }
}










pub fn main() {

    // All the reading is doable at comptime, and I really should do it at then, since the parser shouldn't be editable by config files
    let prec_txt = fs::read_to_string(Path::new("../resources/precedence.txt")).unwrap();
    let prec_lines = prec_txt.split('\n').filter(|x| *x != "").collect::<Vec<&str>>();

    let sym_txt = fs::read_to_string(Path::new("../resources/symbols.txt")).unwrap();
    let syms = sym_txt.split('\n').collect::<Vec<&str>>();


    let p_dat : ParseDat = { // So that this stays a let
        let whitespaces : Vec<char> = syms[2].split(',').map(|x| (*x).chars().nth(0).unwrap()).collect();
        let punc : Vec<char> = syms[0].split(',').map(|x| (*x).chars().nth(0).unwrap()).collect();
        let pref_ops : Vec<char> = syms[4].split(',').map(|x| (*x).chars().nth(0).unwrap()).collect();
        let ops : Vec<char> = prec_txt.split(['\n', ',']).filter(|x| x.len()  > 0).map(|x| x.chars().nth(0).unwrap()).collect();
        ParseDat {whitespaces : whitespaces, punc : punc, pref_ops : pref_ops, ops : ops}
    };




    
    println!("{:?}", p_dat.whitespaces);



    
    let precs : AHashMap<char, u32> = { // AHashMap is faster than std hashmap
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

    let lex_stop : Vec<char> = p_dat.ops.iter().map(|x| *x)
        .chain(p_dat.pref_ops.iter().map(|x| *x))
        .chain(syms[1]
               .split(',')
               .filter(|x| x.len() > 0)
               .map(|x| (*x).chars().nth(0).unwrap()))
        .chain([',', '\n']).collect();

    println!("{:?}", tokenize(part_file(&String::from(syms[6]), &lex_stop), &p_dat));
}

fn part_file(inp : &String, lex_stop : &Vec<char>) -> Vec<String> {
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

fn tokenize(inp : Vec<String>, p_dat : &ParseDat) -> Vec<Token> {
    let mut result : Vec<Token> = Vec::new();
    
    for s in inp.into_iter() {
        if (b'0'..b'9').any(|x| x as char == s.chars().nth(0).unwrap()) {
            if s.contains('.') {
                result.push(Token {kind : TKind::FloatLit, val : s});
            } else {
                result.push(Token {kind : TKind::IntLit, val : s});
            }
        } else if s.chars().nth(0).unwrap() == '\"' && s.chars().last().unwrap() == '\"' {
            result.push(Token {kind : TKind::StrLit, val : s});
        } else if p_dat.punc.contains(&s.chars().nth(0).unwrap()) {
            result.push(Token {kind : TKind::Punc, val : s});
        } else if p_dat.ops.contains(&s.chars().nth(0).unwrap()) {
            result.push(Token {kind : TKind::Op, val : s});
        } else if p_dat.pref_ops.contains(&s.chars().nth(0).unwrap()) {
            result.push(Token {kind : TKind::PrefOp, val : s});
        } else if !p_dat.whitespaces.contains(&s.chars().nth(0).unwrap()) {
            result.push(Token {kind : TKind::Ident, val : s});
        }
    }
    return result;
}
