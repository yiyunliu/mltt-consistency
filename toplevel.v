From WR Require Import syntax common syntactic_soundness typing join.
Module grade : grade_sig.
  Import Order.NatOrder.
  Definition display := nat_display.
  Definition grade := Datatypes_nat__canonical__Order_Lattice.
  Definition el : grade := 0.
End grade.

Module syntax : syntax_sig grade.
  Include (syntax_sig grade).
End syntax.

Module common : common_sig grade syntax.
  Include (common_sig grade syntax).
End common.

Module join : join_sig grade syntax common.
  Include (join_sig grade syntax common).
End join.

Module typing : typing_sig grade syntax common join.
  Include (typing_sig grade syntax common join).
End typing.

Module soundness_syn :=
  syntactic_soundness grade syntax common join typing.
