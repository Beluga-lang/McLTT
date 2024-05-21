Ltac eexists_rel_exp :=
  eexists;
  eexists; [eassumption |];
  eexists.

Ltac eexists_rel_subst :=
  eexists;
  eexists; [eassumption |];
  eexists;
  eexists; [eassumption |].
