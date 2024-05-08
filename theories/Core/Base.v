#[global] Declare Scope mcltt_scope.
#[global] Delimit Scope mcltt_scope with mcltt.
#[global] Bind Scope mcltt_scope with Sortclass.

#[global] Declare Custom Entry judg.

Notation "{{ x }}" := x (at level 0, x custom judg at level 99, format "'{{'  x  '}}'").
