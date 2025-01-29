void Closure::produce_rewritten_clause_lrat_and_clean (std::vector<LitClausePair> &litIds, Rewrite rew1, Rewrite rew2, int except_lhs) {
  for (auto &litId : litIds){
    litId.clause = produce_rewritten_clause_lrat (litId.clause, rew1, rew2, except_lhs);
  }
  litIds.erase (std::remove_if (begin (litIds), end (litIds), [](const LitClausePair& p) { return !p.clause; }), end (litIds));
}

void Closure::produce_rewritten_clause_lrat_and_clean (std::vector<LitClausePair> &litIds, Rewrite rew1, Rewrite rew2) {
  for (auto &litId : litIds){
    litId.clause = produce_rewritten_clause_lrat (litId.clause, rew1, rew2);
  }
  litIds.erase (std::remove_if (begin (litIds), end (litIds), [](const LitClausePair& p) { return !p.clause; }), end (litIds));
}

Clause *Closure::produce_rewritten_clause_lrat (Clause *c, Rewrite rew1, Rewrite rew2, int except_lhs) {
  if (!c)
    return nullptr;
  Clause *d = produce_rewritten_clause (c, rew1, rew2, except_lhs);
  if (!d)
    return nullptr;
  if (internal->lrat) {
    internal->lrat_chain.push_back (c->id);
    internal->lrat_chain.push_back (d->id);
  }
  return d;
}

Clause *Closure::produce_rewritten_clause_lrat (Clause *c, Rewrite rew1, Rewrite rew2) {
  if (!c)
    return nullptr;
  Clause *d = produce_rewritten_clause (c, rew1, rew2);
  if (!d)
    return nullptr;
  if (internal->lrat) {
    internal->lrat_chain.push_back (c->id);
    internal->lrat_chain.push_back (d->id);
  }
  return d;
}
