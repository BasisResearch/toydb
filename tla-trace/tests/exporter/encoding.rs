// Regression model for the Observe wire format. See README.md for regeneration.
use vstd::prelude::*;
verus! {
pub struct Record {
    pub tag: nat,
    pub tag_: nat,
    pub unit: (),
}
pub enum Choice {
    A { tag: nat },
    B,
}
pub struct State {
    pub record: Record,
    pub choice: Choice,
}
pub open spec fn init(s: State) -> bool {
    s.record == Record { tag: 0, tag_: 7, unit: () }
    && s.choice == Choice::A { tag: 0 }
}
pub open spec fn t_set(pre: State, post: State, r#type: nat) -> bool {
    post.record == Record { tag: r#type, tag_: pre.record.tag_, unit: () }
    && post.choice == Choice::A { tag: r#type }
}
pub open spec fn next(pre: State, post: State) -> bool {
    exists|n: nat| 1 <= n && n <= 2 && t_set(pre, post, n)
}
}
