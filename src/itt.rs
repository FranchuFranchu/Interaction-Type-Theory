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
// Con node, used for lambdas and applications
pub const CON : u32 = 2;
// Annotation node, used for thetas and annotations
pub const ANN : u32 = 3;
// Equal node, used for equality checks. Back-commutes
pub const EQL : u32 = 4;
// Fixpoint node. Back-commutes
pub const FIX : u32 = 5;
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
  if kind(inet, x) == ANN {
    println!("> {}", equal(inet, enter(inet, port(x, 1)), enter(inet, port(y, 1))));
    println!("> {}", equal(inet, enter(inet, port(x, 2)), enter(inet, port(y, 2))));
  }
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
    println!("{:?}", slot(next));
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
        if x_back {
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
          Some(Self::BackCommute(slot(x)))
        } else if y_back {
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
  let mut old_ann: Option<(u32, u32)> = None;
  let mut old_com: Option<(u32, u32, u32, u32)> = None;
  let mut cols = ((1, 2, 3), (5, 6, 3));
  let term = crate::syntax::readback(&inet, 1);
  loop {
    let init_rules = rules;
    for index in 0 .. (inet.nodes.len() / 4) as u32 {
      
      let kind = kind(inet, index);
      if kind != NIL {
        let prev = port(index, 0);
        let next = enter(inet, prev);
        if let Some(active_pair_type) = ActivePairType::from_port(inet, prev) {
          let mut h = std::collections::HashMap::new();
          let a1 = port(index, 1);
          let a2 = port(index, 2);
          let b1 = port(addr(next), 1);
          let b2 = port(addr(next), 2);
          h.insert(prev, cols.0.0);
          h.insert(a2, cols.0.0);
          h.insert(a1, cols.0.0);
          h.insert(next, cols.0.1);
          h.insert(b1, cols.0.1);
          h.insert(b2, cols.0.1);
          if let Some((a0, a1, b0, b1)) = old_com.take() {
            
          }
          if let Some((a, b)) = old_ann.take() {
            h.insert(a, cols.1.2);
            h.insert(b, cols.1.2);
          }
          
          let term = crate::syntax::readback_and_highlight(&inet, 1, &h);
          println!("> {}", term);
          println!("{:?}", active_pair_type);
          rules += 1;
          match active_pair_type {
            ActivePairType::Annihilate => annihilate(inet, addr(prev), addr(next)),
            ActivePairType::Commute => commute(inet, addr(prev), addr(next)),
            ActivePairType::Cross(k) => cross(inet, addr(prev), addr(next), k),
            ActivePairType::BackCommute(p) => back_commute(inet, addr(prev), addr(next), p),
            ActivePairType::ReverseBackCommute(p) => back_commute(inet, addr(next), addr(prev), p),
          };
          
          cols = (cols.1, cols.0);
          
          break;
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

// Compares two ports for equivalence.
pub fn equal(inet: &mut INet, a: Port, b: Port) -> bool {
  let mut aP = &mut BTreeMap::new();
  let mut bP = &mut BTreeMap::new();
  let mut aL = &mut Vec::new();
  let mut bL = &mut Vec::new();
  return compare(inet, 0, true, a, a, aP, aL, b, b, bP, bL);
}

// Comparison algorithm.
// Aliases: R = root, P = path, L = logs, S = slot, K = kind
pub fn compare(inet: &mut INet, step: u32, flip: bool,
  a0: Port, aR: Port, aP: &mut Path, aL: &mut Logs,
  b0: Port, bR: Port, bP: &mut Path, bL: &mut Logs,
) -> bool {
  // FIXME: still can't handle loops, so we just halt deep recs for now
  let halt = 8192;
  let step = step + 1;
  

  let a1 = enter(inet, a0);
  let aS = slot(a1);
  let aK = kind(inet, addr(a1));

  //println!("- leap {} {} | {}:{}->{}:{} {}:{} | aR={}:{} | {:?} {:?}", step, flip, addr(a0), slot(a0), addr(a1), slot(a1), addr(b0), slot(b0), addr(aR), slot(aR), aP, bP);
  //limit(1000000);

  // If on root...
  if step > halt {
    panic!("{:?}", "Loop detected!");
  }
  if a1 == aR || a1 == ROOT {
    // If didn't move 'b' yet, flip and recurse...
    if flip {
      return compare(inet, 0, false, b0, bR, bP, bL, a0, aR, aP, aL);
    // Otherwise, compare this leap...
    } else {
      let av = aP.get(&CON).map_or(0, |vec| vec.len());
      let bv = bP.get(&CON).map_or(0, |vec| vec.len());
      return av == bv;
    }
  }

  // If entering main port...
  if aS == 0 {
    if (aK == ERA) {
      println!("{:?}", aK);
      return false
    } 
    // If deque isn't empty, pop_back a slot and move to it
    if let Some(slot) = aP.get_mut(&aK).and_then(|vec| vec.pop_back()) {
      aL.push(format!("down({}:{})", addr(a1), slot));
      let a0 = port(addr(enter(inet, a0)), slot as u32);
      let eq = compare(inet, step, flip, a0, aR, aP, aL, b0, bR, bP, bL);
      aL.pop();
      aP.entry(aK).or_default().push_back(slot);
      return eq;

    // If deque is empty, move to slots [1,2] and push_front to the *other* deque
    } else {
      for slot in [2, 1] {
        aL.push(format!("choose({}:{})", addr(a1), slot));
        bP.entry(aK).or_default().push_front(slot);
        let a0 = port(addr(enter(inet, a0)), slot as u32);
        let eq = compare(inet, step, flip, a0, aR, aP, aL, b0, bR, bP, bL);
        aL.pop();
        bP.get_mut(&aK).and_then(|vec| vec.pop_front());
        if !eq { return false; }
      }
      return true;
    }
  }

  // If entering an aux port, push_back that slot to the deque, and move to the main port
  if aS > 0 {
    aL.push(format!("up({})", aS));
    aP.entry(aK).or_default().push_back(slot(enter(inet, a0)) as u8);
    let a0 = port(addr(enter(inet, a0)), 0);
    let eq = compare(inet, step, flip, a0, aR, aP, aL, b0, bR, bP, bL);
    aP.get_mut(&aK).and_then(|vec| vec.pop_back());
    aL.pop();
    return eq;
  }

  unreachable!();
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
