use std::collections::BTreeMap;
use std::collections::VecDeque;

type Path = BTreeMap<u32, VecDeque<u8>>;
type Logs = Vec<String>;

#[derive(Clone, Debug)]
pub struct INet {
  pub nodes: Vec<u32>,
  pub reuse: Vec<u32>,
  pub rules: u32,
}

// Node types are consts because those are used in a Vec<u32>.
pub const TAG : u32 = 28;
pub const NIL : u32 = 0;
// Erase node
pub const ERA : u32 = 1;
// Annotation node, used for thetas and annotations
pub const ANN : u32 = 2;
// Equal node, used for equality checks. Back-commutes
pub const EQL : u32 = 3;
// Fixpoint node. Back-commutes
pub const FIX : u32 = 4;
// Con node, used for lambdas and applications
pub const CON : u32 = 5;
// Duplication node. Front-commutes
pub const DUP : u32 = 6;

// ROOT is port 1 on address 0.
pub const ROOT : u32 = 1;

// A port is just a u32 combining address (30 bits) and slot (2 bits).
pub type Port = u32;

// Create a new net with a root node.
pub fn new_inet() -> INet {
  let mut inet = INet { nodes: vec![], reuse: vec![], rules: 0 };
  let root = new_node(&mut inet, 0);
  link(&mut inet, port(root, 0), port(root, 2));
  link(&mut inet, port(root, 1), port(root, 1));
  return inet;
}

// Allocates a new node, reclaiming a freed space if possible.
pub fn new_node(inet: &mut INet, kind: u32) -> u32 {
  let node : u32 = match inet.reuse.pop() {
    Some(index) => index,
    None => {
      let len = inet.nodes.len();
      inet.nodes.resize(len + 4, 0);
      (len as u32) / 4
    }
  };
  inet.nodes[port(node, 0) as usize] = port(node, 0);
  inet.nodes[port(node, 1) as usize] = port(node, 1);
  inet.nodes[port(node, 2) as usize] = port(node, 2);
  inet.nodes[port(node, 3) as usize] = kind;
  return node;
}

pub fn erase(inet: &mut INet, node: u32) {
  inet.reuse.push(node);
  inet.nodes[port(node, 0) as usize] = 0;
  inet.nodes[port(node, 1) as usize] = 0;
  inet.nodes[port(node, 2) as usize] = 0;
  inet.nodes[port(node, 3) as usize] = NIL;
}

// Builds a port (an address / slot pair).
pub fn port(node: u32, slot: u32) -> Port {
  (node << 2) | slot
}

// Returns the address of a port (TODO: rename).
pub fn addr(port: Port) -> u32 {
  port >> 2
}

// Returns the slot of a port.
pub fn slot(port: Port) -> u32 {
  port & 3
}

// Enters a port, returning the port on the other side.
pub fn enter(inet: &INet, port: Port) -> Port {
  inet.nodes[port as usize]
}

// Enters a slot on the node pointed by this port.
pub fn get(inet: &INet, p: Port, s: u32) -> Port {
  enter(inet, port(addr(p), s))
}

// Gets the kind of the node.
pub fn kind(inet: &INet, node: u32) -> u32 {
  inet.nodes[port(node, 3) as usize]
}

// Links two ports.
pub fn link(inet: &mut INet, ptr_a: u32, ptr_b: u32) {
  inet.nodes[ptr_a as usize] = ptr_b;
  inet.nodes[ptr_b as usize] = ptr_a;
}

pub fn should_back_commute(x: u32) -> bool {
  x == EQL || x == FIX
}
pub fn should_back_annihilate(x: u32) -> bool {
  x == EQL
}

pub fn should_annihilate(mut x: u32, mut y: u32) -> bool {
  x == y
}

// Annihilation interaction.
// ---|\     /|---    ---, ,---
//    | |---| |    =>     X
// ---|/     \|---    ---' '---
fn annihilate(inet: &mut INet, x: u32, y: u32) {
  link(inet, enter(inet, port(x, 1)), enter(inet, port(y, 1)));
  link(inet, enter(inet, port(x, 2)), enter(inet, port(y, 2)));
  erase(inet, x);
  erase(inet, y);
}

// Commute interaction.
//                        /|-------|\
//                    ---|#|       | |---
// ---|\     /|---        \|--, ,--|/
//    | |---|#|    =>          X
// ---|/     \|---        /|--' '--|\
//                    ---|#|       | |---
//                        \|-------|/
fn commute(inet: &mut INet, x: u32, y: u32) {
  let a = new_node(inet, kind(inet, x));
  let b = new_node(inet, kind(inet, y));
  link(inet, port(b, 0), enter(inet, port(x, 1)));
  link(inet, port(y, 0), enter(inet, port(x, 2)));
  link(inet, port(a, 0), enter(inet, port(y, 1)));
  link(inet, port(x, 0), enter(inet, port(y, 2)));
  link(inet, port(a, 1), port(b, 1));
  link(inet, port(a, 2), port(y, 1));
  link(inet, port(x, 1), port(b, 2));
  link(inet, port(x, 2), port(y, 2));
}

// Back-Commute interaction.
//                        /|-------|\
//    x      y        ---|#|       | |---
// ---|\     /|---        \|--, ,--|/
//    | |---|#|    =>          X
// ---|/     \|---        /|--' '--|\
//                    ---|#|       | |---
//                        \|-------|/
//
//     y     x                   a
// ---|\                      ---|\       
//    | |---|\                   |#|,  b  
// ---|/    |#|--- =>      ---, ,|/  '|\     
//----------|/                 X      | |-----
//                        /|, / '|\  ,|/
//                    ---| | X   |#|'
//                        \|' '--|/    
//                         y      x
//
fn back_commute(inet: &mut INet, x: u32, y: u32, p: u32) {
  let (p1, p2) = if p == 1 {
    (1, 2)
  } else {
    (2, 1)
  };
  let a = new_node(inet, kind(inet, x));
  let b = new_node(inet, kind(inet, y));
  link(inet, port(b, 0), enter(inet, port(x, 0)));
  link(inet, port(y, 0), enter(inet, port(x, p2)));
  link(inet, port(a, p1), enter(inet, port(y, p1)));
  link(inet, port(x, p1), enter(inet, port(y, p2)));
  link(inet, port(a, p2), port(y, p1));
  link(inet, port(x, p2), port(y, p2));
  link(inet, port(a, 0), port(b, p1));
  link(inet, port(x, 0), port(b, p2));
}

fn cross(inet: &mut INet, x: u32, y: u32, k: u32) {
  let a = new_node(inet, k);
  let b = new_node(inet, k);
  link(inet, port(a, 2), enter(inet, port(x, 1)));
  link(inet, port(a, 1), enter(inet, port(y, 1)));
  link(inet, port(b, 2), enter(inet, port(x, 2)));
  link(inet, port(b, 1), enter(inet, port(y, 2)));
  link(inet, port(a, 0), port(b, 0));
  erase(inet, x);
  erase(inet, y);
}

fn back_annihilate(inet: &mut INet, x: u32, y: u32) {
  link(inet, enter(inet, port(x, 0)), enter(inet, port(y, 0)));
  erase(inet, x);
  erase(inet, y);
}

// Reduces a wire to weak normal form.
pub fn reduce(inet: &mut INet, root: Port) {
  let mut path = vec![];
  let mut prev = root;
  loop {
    let next = enter(inet, prev);
    //println!("------------------------------- {}:{} -> {}:{}", addr(prev), slot(prev), addr(next), slot(next));
    //println!("{}", show(inet));
    //limit(500);

    
    // If next is ROOT, stop.
    if next == ROOT {
      return;
    }
    // If next is a main port...
    if slot(next) == 0 {

      // If prev is a main port, reduce the active pair.
      if slot(prev) == 0 {
        inet.rules += 1;
        rewrite(inet, prev, next);
        prev = path.pop().unwrap();
        continue;
      // Otherwise, return the axiom.
      } else {
        return;
      }
    }
    // If next is an aux port, pass through.
    path.push(prev);
    prev = port(addr(next), 0);
  }
}

// Reduces the net to normal form.
pub fn normal(inet: &mut INet, root: Port) {
  let mut warp = vec![root];
  let mut tick = 0;
  while let Some(prev) = warp.pop() {
    reduce(inet, prev);
    let next = enter(inet, prev);
    let addr = addr(next);
    let kind = kind(inet, addr);
    if slot(next) == 0 {
      warp.push(port(addr, 1));
      warp.push(port(addr, 2));
    }
  }
}
#[derive(Debug, Clone)]
pub enum ActivePairType {
  Annihilate,
  Commute,
  BackAnnihilate,
  Cross(u32),
  BackCommute(u32),
  ReverseBackCommute(u32),
}
impl ActivePairType {
  fn from_port(inet: &INet, x: u32) -> Option<ActivePairType> {
    let y = enter(inet, x);
    let x_kind = kind(inet, addr(x));
    let y_kind = kind(inet, addr(y));
    let x_back = should_back_commute(x_kind) && x_kind != y_kind || should_back_annihilate(x_kind) && x_kind == y_kind;
    let y_back = should_back_commute(y_kind) && x_kind != y_kind || should_back_annihilate(y_kind) && x_kind == y_kind;
    let x_active = (slot(x) == 0) && !x_back || (slot(x) != 0) && x_back;
    let y_active = (slot(y) == 0) && !y_back || (slot(y) != 0) && y_back;
    if x_active && y_active {
      if x_kind == y_kind {
        if x_back && y_back 
        && enter(inet, port(addr(x), 1)) == port(addr(y), 1)
        && enter(inet, port(addr(x), 2)) == port(addr(y), 2) {
          Some(Self::BackAnnihilate)
        } else if x_back {
          None
        } else if y_back {
          None
        } /*else if x_kind == ANN {
          Some(Self::Cross(EQL))
        } */else {
          Some(Self::Annihilate)
        }
      } else {
        if x_back && y_back {
          todo!()
        } else if x_back {
          // disable two-sided commutation
          if slot(x) == 2 {
            return None;
          }
          Some(Self::BackCommute(slot(x)))
        } else if y_back {
          // disable two-sided commutation
          if slot(y) == 2 {
            return None;
          }
          Some(Self::ReverseBackCommute(slot(y)))
        } else {
          Some(Self::Commute)
        }
      }
    } else {
      None
    }
  }
}

// Eager reduction
// FIXME: wrote this quickly to test the checker, obviously very inefficient
pub fn eager(inet: &mut INet) {
  let mut rules = 0;
  let mut cols = ((1, 2, 3),);
  let term = crate::syntax::readback(&inet, 1);
  loop {
    let init_rules = rules;
    for index in 0 .. (inet.nodes.len() / 4) as u32 {
      
      let kind = kind(inet, index);
      if kind != NIL {
        for slot in 0..=2 {
          let prev = port(index, slot);
          let next = enter(inet, prev);
          if let Some(active_pair_type) = ActivePairType::from_port(inet, prev) {
            let mut h = std::collections::HashMap::new();
            h.insert(prev, cols.0.0);
            h.insert(next, cols.0.1);
            
            let term = crate::syntax::readback_and_highlight(&inet, 1, &h);
            println!("> {}", term);
            println!("{:?}", active_pair_type);
            rules += 1;
            match active_pair_type {
              ActivePairType::Annihilate => annihilate(inet, addr(prev), addr(next)),
              ActivePairType::Commute => commute(inet, addr(prev), addr(next)),
              ActivePairType::Cross(k) => cross(inet, addr(prev), addr(next), k),
              ActivePairType::BackAnnihilate => back_annihilate(inet, addr(prev), addr(next)),
              ActivePairType::BackCommute(p) => back_commute(inet, addr(prev), addr(next), p),
              ActivePairType::ReverseBackCommute(p) => back_commute(inet, addr(next), addr(prev), p),
            };
            
            break;
          }
        }
      }
    }
    if rules == init_rules {
      break;
    }
  }
}

// Rewrites an active pair.
pub fn rewrite(inet: &mut INet, x: Port, y: Port) {
  //println!(">> rewrite {}:{}/{} {}:{}/{}", addr(x), slot(x), kind(inet, addr(x)), addr(y), slot(y), kind(inet, addr(y)));
  if should_back_commute(kind(inet, addr(x))) && !should_back_commute(kind(inet, addr(y))) {
    back_commute(inet, x, y, 1)
  } else {
    if (kind(inet, addr(x)) == kind(inet, addr(y))) {
      annihilate(inet, addr(x), addr(y));
    } else {
      commute(inet, addr(x), addr(y));
    } 
  }
}

// Debugger
// --------

pub fn show_tree(inet: &INet, prev: Port, names: &mut BTreeMap<u32,String>) -> String {
  let next = enter(inet, prev);
  let kind = kind(inet, addr(next));
  //println!("tree {}:{} -> {}:{} | {}", addr(prev), slot(prev), addr(next), slot(next), kind);
  if next == ROOT {
    return "@".to_string();
  }
  if slot(next) == 0 {
    //if kind == ERA {
      //return format!("*");
    //} else {
      let a = show_tree(inet, port(addr(next), 1), names);
      let b = show_tree(inet, port(addr(next), 2), names);
      let p = match kind {
        ERA => ('«', '»'),
        CON => ('(', ')'),
        ANN => ('[', ']'),
        _   => ('{', '}'),
      };
      return format!("\x1b[2m{}\x1b[0m\x1b[1m{}\x1b[0m{} {}\x1b[1m{}\x1b[0m", addr(next), p.0, a, b, p.1);
    //}
  }
  if let Some(name) = names.get(&prev) {
    return name.to_string();
  } else {
    let name = crate::syntax::index_to_name(names.len() as u32 + 1);
    let name = String::from_utf8_lossy(&name).to_string();
    //let name = format!("{}#{}:{}", name, addr(next), slot(next));
    names.insert(next, name.clone());
    return format!("{}", name);
  }
}

pub fn show(inet: &INet) -> String {
  let mut names = &mut BTreeMap::new();
  let mut lines = String::new();
  for index in 1 .. (inet.nodes.len() / 4) as u32 {
    let prev = port(index, 0);
    let next = enter(inet, prev);
    let kind = kind(inet, addr(next));
    if next != 0 {
      if next == ROOT {
        lines.push_str(&format!("^─{}\n", show_tree(inet, next, names)));
      //} else if kind == ERA {
        //lines.push_str(&format!("*─{}\n", show_tree(inet, next, names)));
      } else if addr(prev) < addr(next) && slot(prev) == 0 && slot(next) == 0 {
        lines.push_str(&format!("┌─{}\n", show_tree(inet, prev, names)));
        lines.push_str(&format!("└─{}\n", show_tree(inet, next, names)));
      }
    }
  }
  return lines;
}

pub fn limit(lim: i32) {
  static mut COUNTER: i32 = 0;
  unsafe {
    COUNTER += 1;
    if COUNTER >= lim {
      println!("{:?}", "Loop detected");
      std::process::exit(0);
    }
  }
}
