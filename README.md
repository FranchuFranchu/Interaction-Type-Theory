# Equality algorithm

This algorithm checks whether two terms are equal by self-annihilating them with a special "EQL" node which commutes "backwards". 

If they don't self-annihilate, some EQL nodes will still remain. This means that the terms aren't equal.

Try out `cargo run sample.itt`. `?{a b}` is the builder for EQL nodes.

Implementation based on Taelin's `Interaction-Type-Theory` experimental program.