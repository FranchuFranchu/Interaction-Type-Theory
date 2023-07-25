#![allow(dead_code)]

#[derive(Clone, Debug)]
pub struct INet {
  pub nodes: Vec<u32>,
  pub reuse: Vec<u32>,
  pub rules: u32,
}

// Node types are consts because those are used in a Vec<u32>.
pub const TAG : u32 = 28;
pub const ERA : u32 = 0;
pub const ANN : u32 = 1;
pub const CON : u32 = 2;
pub const FIX : u32 = 3;
pub const DUP : u32 = 4;

// ROOT is port 1 on address 0.
pub const ROOT : u32 = 1;

// A port is just a u32 combining address (30 bits) and slot (2 bits).
pub type Port = u32;

// Create a new net with a root node.
pub fn new_inet() -> INet {
  INet {
    nodes: vec![2,1,0,0],
    reuse: vec![],
    rules: 0
  }
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

// Kind of the node.
pub fn kind(inet: &INet, node: u32) -> u32 {
  inet.nodes[port(node, 3) as usize]
}

// Links two ports.
pub fn link(inet: &mut INet, ptr_a: u32, ptr_b: u32) {
  inet.nodes[ptr_a as usize] = ptr_b;
  inet.nodes[ptr_b as usize] = ptr_a;
}

// Reduces a wire to weak normal form.
pub fn reduce(inet: &mut INet, root: Port, skip: &dyn Fn(u32,u32) -> bool) {
  let mut path = vec![];
  let mut prev = root;
  loop {
    let next = enter(inet, prev);
    // If next is ROOT, stop.
    if next == ROOT {
      return;
    }
    // If next is a main port...
    if slot(next) == 0 {
      // Checks if caller asked to skip this rule.
      let skipped = skip(kind(inet,addr(prev)), kind(inet,addr(next)));
      // If prev is a main port, reduce the active pair.
      if slot(prev) == 0 && !skipped {
        inet.rules += 1;
        rewrite(inet, addr(prev), addr(next));
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
    reduce(inet, prev, &|ak,bk| false);
    let next = enter(inet, prev);
    if slot(next) == 0 {
      warp.push(port(addr(next), 1));
      warp.push(port(addr(next), 2));
    }
  }
}

// Rewrites an active pair.
pub fn rewrite(inet: &mut INet, x: Port, y: Port) {
  if kind(inet, x) == kind(inet, y) {
    let p0 = enter(inet, port(x, 1));
    let p1 = enter(inet, port(y, 1));
    link(inet, p0, p1);
    let p0 = enter(inet, port(x, 2));
    let p1 = enter(inet, port(y, 2));
    link(inet, p0, p1);
    inet.reuse.push(x);
    inet.reuse.push(y);
  } else {
    let t = kind(inet, x);
    let a = new_node(inet, t);
    let t = kind(inet, y);
    let b = new_node(inet, t);
    let t = enter(inet, port(x, 1));
    link(inet, port(b, 0), t);
    let t = enter(inet, port(x, 2));
    link(inet, port(y, 0), t);
    let t = enter(inet, port(y, 1));
    link(inet, port(a, 0), t);
    let t = enter(inet, port(y, 2));
    link(inet, port(x, 0), t);
    link(inet, port(a, 1), port(b, 1));
    link(inet, port(a, 2), port(y, 1));
    link(inet, port(x, 1), port(b, 2));
    link(inet, port(x, 2), port(y, 2));
  }
}

use std::collections::HashMap;

type Paths = HashMap<u32, Vec<u8>>;

// Checks if an interaction combinator net is coherent
pub fn check(inet: &mut INet, prev: Port) -> bool {
  is_coherent(inet, prev, &mut HashMap::new(), &mut HashMap::new())
}

// Checks if an interaction combinator net is coherent
fn is_coherent(inet: &mut INet, prev: Port, stacks: &mut Paths, queues: &mut Paths) -> bool {

  // Gets next port attributes
  let next = enter(inet, prev);
  let kind = kind(inet, addr(next));
  let slot = slot(next);

  // If next is root, we completed a leap
  if next == ROOT {
    // If leap is ann-symmetric, then it must be con-symmetric
    if is_symmetric(stacks, queues, ANN) {
      return is_symmetric(stacks, queues, CON);
    // Otherwise, this is an irrelevant leap
    } else {
      return true;
    }
  }

  // If next is erasure, turn around
  if kind == ERA {
    return is_coherent(inet, port(addr(next), 0), stacks, queues);
  }
  println!("{:?} {:?}", slot, kind);
  // If entering a main port...
  if slot == 0 {
    // If stack isn't empty, pop from stack and go to that port
    if let Some(d) = stacks.get_mut(&kind).and_then(|v| v.pop()) {
      let ed = is_coherent(inet, port(addr(next), d as u32), stacks, queues);
      stacks.get_mut(&kind).unwrap().push(d);
      return ed;
    // Otherwise, go to both aux ports and prepend them to queue
    } else {
      queues.entry(kind).or_default().push(1);
      let e1 = is_coherent(inet, port(addr(next), 1), stacks, queues);
      queues.get_mut(&kind).unwrap().pop();
      queues.get_mut(&kind).unwrap().push(2);
      let e2 = is_coherent(inet, port(addr(next), 2), stacks, queues);
      queues.get_mut(&kind).unwrap().pop();
      return e1 && e2;
    }
  } else {
    stacks.entry(kind).or_default().push(slot as u8);
    let e0 = is_coherent(inet, port(addr(next), 0), stacks, queues);
    stacks.get_mut(&kind).unwrap().pop();
    return e0;
  }
}

// A leap is X-symmetric if it its X-stack and X-queue are identical
fn is_symmetric(stacks: &mut Paths, queues: &mut Paths, kind: u32) -> bool {
  match (stacks.get(&kind), queues.get(&kind)) {
    (Some(stack), Some(queue)) => queue.iter().rev().eq(stack.iter()),
    (None, Some(queue)) => queue.is_empty(),
    (Some(stack), None) => stack.is_empty(),
    (None, None) => true,
  }
}

// Debugger
pub fn show(inet: &INet, prev: Port) -> String {
  let next = enter(inet, prev);
  if next == ROOT {
    "".to_string()
  } else {
    let slot_next = slot(next);
    if slot_next == 0 {
      let a = show(inet, port(addr(next), 1));
      let b = show(inet, port(addr(next), 2));
      let k = kind(inet, addr(next));
      if k == ERA {
        format!("*")
      } else {
        let p = if k == CON {
          ('(', ')')
        } else if k == ANN {
          ('[', ']')
        } else if k >= DUP {
          ('{', '}')
        } else {
          ('?', '?')
        };
        format!("\x1b[2m{}\x1b[0m\x1b[1m{}\x1b[0m{} {}\x1b[1m{}\x1b[0m", addr(next), p.0, a, b, p.1)
      }
    } else {
      let x = show(inet, port(addr(next), 0));
      format!("{}\x1b[34m{}\x1b[0m", x, if slot_next == 1 { '<' } else { '>' })
    }
  }
}
