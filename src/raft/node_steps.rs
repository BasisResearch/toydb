//! Attribute-based boundary between the shell and the verified core. A core
//! call can implement zero, one or several model transitions; events lists
//! preserve their order and their partial intermediate observations. The
//! cluster is the traced object, since Raft's model includes its whole network.
use super::*;
use crate::raft::log::Entry;
#[cfg(feature = "tla-trace")]
use tla_trace::{Event, Value};

pub(super) struct Model<'a> {
    pub abs: &'a mut refine::Abs,
    pub log: &'a mut Log,
}

#[cfg(feature = "tla-trace")]
impl Model<'_> {
    fn event(&mut self, step: &str, params: Value, omit: &[&str]) -> Event {
        Event::new(
            step,
            params,
            self.abs.tla_state(self.log, omit).expect("tla-trace: reading log"),
        )
    }
    fn local(&mut self, step: &str) -> Event {
        self.event(step, Value::object([("i", Value::from(self.abs.tla_rank()))]), &[])
    }
}

impl Model<'_> {
    #[cfg(feature = "tla-trace")]
    #[tla_trace::instrument::trace_step(log = tla_trace::thread_log(), events = vec![
        self.event("t_restart", Value::object([
            ("i", Value::from(self.abs.tla_rank())),
            ("commit", Value::from(self.log.get_commit_index().0)),
        ]), &[])
    ])]
    pub fn restart(&mut self) {}

    #[cfg_attr(feature = "tla-trace", tla_trace::instrument::trace_step(log = tla_trace::thread_log(), events =
        if matches!(result, Ok(true)) { vec![self.event("t_bump_term", Value::object([
            ("i", Value::from(self.abs.tla_rank())), ("term", Value::from(term)),
        ]), &[])] } else { vec![] }
    ))]
    pub fn bump_term(&mut self, term: Term) -> Result<bool> {
        self.abs.bump_term(self.log, term)
    }

    #[cfg_attr(feature = "tla-trace", tla_trace::instrument::trace_step(log = tla_trace::thread_log(), events = vec![self.local("t_step_down")]))]
    pub fn step_down(&mut self) {
        self.abs.step_down(self.log);
    }

    #[cfg_attr(feature = "tla-trace", tla_trace::instrument::trace_step(log = tla_trace::thread_log(), events =
        if result.is_ok() { vec![self.local("t_campaign")] } else { vec![] }
    ))]
    pub fn campaign(&mut self) -> Result<refine::CampaignPlan> {
        self.abs.campaign(self.log)
    }

    #[cfg_attr(feature = "tla-trace", tla_trace::instrument::trace_step(log = tla_trace::thread_log(), events =
        if matches!(result, Ok(true)) { vec![self.event("t_grant", Value::object([
            ("v", Value::from(self.abs.tla_rank())), ("c", Value::from(self.abs.tla_rank_of(from))),
            ("term", Value::from(term)),
        ]), &[])] } else { vec![] }
    ))]
    pub fn grant(&mut self, from: NodeID, term: Term, last: Index, lterm: Term) -> Result<bool> {
        self.abs.grant(self.log, from, term, last, lterm)
    }

    #[cfg_attr(feature = "tla-trace", tla_trace::instrument::trace_step(log = tla_trace::thread_log(), events = vec![
        self.event("t_collect_vote", Value::object([
            ("i", Value::from(self.abs.tla_rank())), ("v", Value::from(self.abs.tla_rank_of(from))),
        ]), &[])
    ]))]
    pub fn collect_vote(&mut self, from: NodeID, term: Term) -> bool {
        self.abs.collect_vote(self.log, from, term)
    }

    #[cfg_attr(feature = "tla-trace", tla_trace::instrument::trace_step(log = tla_trace::thread_log(), events =
        if result.is_ok() { vec![self.local("t_become_leader")] } else { vec![] }
    ))]
    pub fn become_leader(&mut self) -> Result<Index> {
        self.abs.become_leader(self.log)
    }

    #[cfg_attr(feature = "tla-trace", tla_trace::instrument::trace_step(log = tla_trace::thread_log(), events = {
        let mut events = vec![];
        if let Ok(plan) = &result {
            let i = Value::from(self.abs.tla_rank());
            let omit: &[&str] = if plan.committed { &["commit"] } else { &[] };
            if plan.match_index != 0 { events.push(self.event("t_send_ack", Value::object([
                ("i", i.clone()), ("mi", Value::from(plan.match_index)),
            ]), omit)); }
            if read_seq >= 1 { events.push(self.event("t_confirm_read", Value::object([
                ("i", i.clone()), ("term", Value::from(term)), ("seq", Value::from(read_seq)),
            ]), omit)); }
            if plan.committed { events.push(self.event("t_recv_commit", Value::object([
                ("i", i), ("ci", Value::from(commit_index)), ("mi", Value::from(last_index)),
            ]), &[])); }
        }
        events
    }))]
    pub fn follower_heartbeat(
        &mut self,
        term: Term,
        last_index: Index,
        commit_index: Index,
        read_seq: u64,
    ) -> Result<refine::HeartbeatPlan> {
        self.abs.follower_heartbeat(self.log, term, last_index, commit_index, read_seq)
    }

    #[cfg_attr(feature = "tla-trace", tla_trace::instrument::trace_step(log = tla_trace::thread_log(), events =
        if let Ok(refine::AppendPlan::Accept { match_index }) = &result { vec![self.event("t_recv_append", Value::object([
            ("i", Value::from(self.abs.tla_rank())), ("term", Value::from(term)),
            ("base", Value::from(base)), ("bterm", Value::from(bterm)), ("mi", Value::from(*match_index)),
        ]), &[])] } else { vec![] }
    ))]
    pub fn follower_append(
        &mut self,
        term: Term,
        base: Index,
        bterm: Term,
        entries: Vec<Entry>,
    ) -> Result<refine::AppendPlan> {
        self.abs.follower_append(self.log, term, base, bterm, entries)
    }

    #[cfg_attr(feature = "tla-trace", tla_trace::instrument::trace_step(log = tla_trace::thread_log(), events =
        if result >= 1 { vec![self.event("t_confirm_read", Value::object([
            ("i", Value::from(self.abs.tla_rank())), ("term", Value::from(term)), ("seq", Value::from(result)),
        ]), &[])] } else { vec![] }
    ))]
    pub fn follower_read(&mut self, term: Term, seq: u64) -> u64 {
        self.abs.follower_read(self.log, term, seq)
    }

    #[cfg_attr(feature = "tla-trace", tla_trace::instrument::trace_step(log = tla_trace::thread_log(), events =
        if result.is_ok() { vec![self.local("t_propose")] } else { vec![] }
    ))]
    pub fn propose(&mut self, command: Option<Vec<u8>>) -> Result<Index> {
        self.abs.propose(self.log, command)
    }

    #[cfg_attr(feature = "tla-trace", tla_trace::instrument::trace_step(log = tla_trace::thread_log(), events = vec![self.local("t_submit_read")]))]
    pub fn submit_read(&mut self) -> u64 {
        self.abs.submit_read(self.log)
    }

    #[cfg_attr(feature = "tla-trace", tla_trace::instrument::trace_step(log = tla_trace::thread_log(), events =
        if result.commit_index >= 1 { vec![self.event("t_send_commit", Value::object([
            ("i", Value::from(self.abs.tla_rank())), ("ci", Value::from(result.commit_index)),
        ]), &[])] } else { vec![] }
    ))]
    pub fn leader_heartbeat(&mut self) -> refine::HeartbeatMsg {
        self.abs.leader_heartbeat(self.log)
    }

    #[cfg_attr(feature = "tla-trace", tla_trace::instrument::trace_step(log = tla_trace::thread_log(), events =
        if let Ok(Some(ci)) = result { vec![
            self.event("t_send_ack", Value::object([
                ("i", Value::from(self.abs.tla_rank())), ("mi", Value::from(self.log.get_last_index().0)),
            ]), &["commit"]),
            self.event("t_leader_commit", Value::object([
                ("i", Value::from(self.abs.tla_rank())), ("ci", Value::from(ci)),
                ("q", self.abs.tla_commit_quorum(self.log, ci)),
            ]), &[]),
        ] } else { vec![] }
    ))]
    pub fn leader_try_commit(&mut self) -> Result<Option<Index>> {
        self.abs.leader_try_commit(self.log)
    }

    #[cfg_attr(feature = "tla-trace", tla_trace::instrument::trace_step(log = tla_trace::thread_log(), events =
        if let Ok(Some(msg)) = &result { vec![self.event("t_send_append", Value::object([
            ("i", Value::from(self.abs.tla_rank())), ("b", Value::from(msg.base_index)),
            ("e", Value::from(msg.base_index + msg.entries.len() as Index)),
        ]), &[])] } else { vec![] }
    ))]
    pub fn leader_send_append(
        &mut self,
        peer: NodeID,
        probe: bool,
        max_entries: usize,
    ) -> Result<Option<refine::AppendMsg>> {
        self.abs.leader_send_append(self.log, peer, probe, max_entries)
    }
}
