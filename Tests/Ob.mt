(* Mathematica Test File *)
singleton777 = {777};
Test[
    Ob[singleton777]
    ,
    ob@Association["object" -> singleton777, "ct" -> ctSymbol[SetCat], "label" -> singleton777]
    ,
    TestID->"Ob-simple"
]
Test[
    Ob[singleton777, "label"->"lucky"]
    ,
    ob@Association["object" -> singleton777, "ct" -> ctSymbol[SetCat], "label" -> "lucky"]
    ,
    TestID->"Ob-label_option_specified"
]

