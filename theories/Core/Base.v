#[global] Declare Scope mctt_scope.
#[global] Delimit Scope mctt_scope with mctt.
#[global] Bind Scope mctt_scope with Sortclass.

#[global] Declare Custom Entry judg.

Notation "{{ x }}" := x (at level 0, x custom judg at level 99, format "'{{'  x  '}}'").
