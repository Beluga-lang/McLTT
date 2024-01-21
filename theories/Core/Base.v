#[global] Declare Scope exp_scope.
#[global] Delimit Scope exp_scope with exp.

#[global] Bind Scope exp_scope with Sortclass.

#[global] Declare Custom Entry judg.
Notation "{{ x }}" := x (at level 0, x custom judg at level 99, format "'{{'  x  '}}'").
