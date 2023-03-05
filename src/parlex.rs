use std::fs;
use std::path::Path;
use std::fmt::{Debug, Formatter, Error};
use std::write;
use std::str::Chars;

extern crate ahash;
use ahash::AHashMap;


trait FLChar {
    fn first_char(&self) -> Option<char>;
    fn last_char(&self) -> Option<char>;
}


impl FLChar for str {
    fn first_char(&self) -> Option<char> {
        return self.chars().nth(0);
    }

    fn last_char(&self) -> Option<char> {
        return self.chars().last();
    }
}

impl FlChar for Token {
    fn first_char(&self) -> Option<char> {
        return self.val.first_char();
    }

    fn last_char(&self) -> Option<char> {
        return self.val.last_char();
    }
}




struct ParseDat {
    whitespaces : Vec<char>,
    punc : Vec<char>,
    pref_ops : Vec<char>,
    ops : Vec<char>,
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

impl Token {
    fn chars(&self) -> Chars<'_> {
        return self.val.chars();
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


impl ParseDat {
    fn tokenize(&mut self, inp : Vec<String>) -> Vec<Token> {
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
            } else if self.punc.contains(&s.chars().nth(0).unwrap()) {
                result.push(Token {kind : TKind::Punc, val : s});
            } else if self.ops.contains(&s.chars().nth(0).unwrap()) {
                result.push(Token {kind : TKind::Op, val : s});
            } else if self.pref_ops.contains(&s.chars().nth(0).unwrap()) {
                result.push(Token {kind : TKind::PrefOp, val : s});
            } else if !self.whitespaces.contains(&s.chars().nth(0).unwrap()) {
                result.push(Token {kind : TKind::Ident, val : s});
            }
        }
        return result;
    }
}


impl ASTNode {
    fn parse_arg(&mut self, lexed : &mut [Token], lastNode : &mut Option<ASTNode>) {
        
        let mut i = 0;
        let mut inOp = false;

        let lxln = lexed.len();

        // This function will handle prefix operators, but will delegate when it encounters a call
        // This function should never recieve something with an infix operator in it

        if lexed[0].first_char().unwrap() == '(' && lexed[0].last_char().unwrap() == ')' {
            if !lexed[1..lxln - 1].iter().map(|x| x.first_char().unwrap()).any(|x| x == '(') {
                self.parse_expr(&mut lexed[1..lxln - 1], lastNode);
                return;
            }
        }

        while (0..lexed.len()).contains(&i) {
            if i + 1 < lexed.len() && lexed[i + 1].first_char().unwrap() == '(' {
                let mut nest_count = 0;
                let mut slice = (i, -1);

                i += 2;

                while nest_count >= 0 {
                    if lexed[i].first_char().unwrap() == '(' {
                        nest_count += 1;
                    } else if lexed[i].first_char() == ')' {
                        nest_count += -1;
                    }
                    i += 1;
                }
                slice[1] = i - 1;
            }
        }
    }

    fn parse_expr(&mut self, lexed : &mut [Token], lastNode : &mut Option<ASTNode>) {
    }
}





pub fn main() {

    // All the reading is doable at comptime, and I really should do it at then, since the parser shouldn't be editable by config files
    let prec_txt = fs::read_to_string(Path::new("../resources/precedence.txt")).unwrap();
    let prec_lines = prec_txt.split('\n').filter(|x| *x != "").collect::<Vec<&str>>();

    let sym_txt = fs::read_to_string(Path::new("../resources/symbols.txt")).unwrap();
    let syms = sym_txt.split('\n').collect::<Vec<&str>>();


    let mut p_dat : ParseDat = {
        let whitespaces : Vec<char> = syms[2].split(',').map(|x| (*x).chars().nth(0).unwrap()).collect();
        let punc : Vec<char> = syms[0].split(',').map(|x| (*x).chars().nth(0).unwrap()).collect();
        let pref_ops : Vec<char> = syms[4].split(',').map(|x| (*x).chars().nth(0).unwrap()).collect();
        let ops : Vec<char> = prec_txt.split(['\n', ',']).filter(|x| x.len() > 0).map(|x| x.chars().nth(0).unwrap()).collect();
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

    let lexed = p_dat.tokenize(part_file(syms[6], &lex_stop));
    println!("{:?}", lexed);
}

fn part_file(inp : &str, lex_stop : &Vec<char>) -> Vec<String> {
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



// So now we have to think about how to parse things

// I already implemented this, but my earlier impl is borderline incomprehensible and I'm gonna try to do it a bit cleaner this time
// Basic outline of the strategy will be to:

// (a) big function called [parse_arg] which will delegate when it encounters a function call or an infix operator
// (b) much smaller function [parse_call] which delegates for every arg that isn't size 1
// (c) similarly large function [parse_expr] which will initially take in the expr and deal with all infix operators.
// I will copy this explanation into the notes file, which I'll put into the root dir

// Also, these should perhaps be methods on ParseDat instead of independent functions, but whatever, who really cares anyway


