(* Mathematica Test File *)
Test[
	Fn[{Reals,Reals}, Sin, "label" -> "sine"]
	,
	fn@Association["dom"->Reals, "cod"->Reals, "function"->Sin, "label"->"sine"]
	,
	TestID->"Fn-label_option_specified"
]
