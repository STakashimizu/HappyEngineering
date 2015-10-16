(* Mathematica Package *)

(* Created by the Wolfram Workbench Oct 4, 2015 *)

BeginPackage["happyEngineering`"]
(* Exported symbols added here with SymbolName::usage *) 

clear::usage = "";
SetCat::usage = "";
NA::usage = "";
(*CenterDot*)
setCt::usage = "";
ctSymbol::usage = "";
getCt::usage = "";
ct::usage = "";
Ct::usage = "";
ob::usage = "";
Ob::usage = "";
comprehension::usage = "";
dom::usage = "";
cod::usage = "";
fn::usage = "";
Fn::usage = "";
ar::usage = "";
Ar::usage = "";
fr::usage = "";
Fr::usage = "";
nt::usage = "";
Nt::usage = "";
power::usage = "";
ctSymbol::usage = "";
$ctDatabase::usage = "";
$workingCat::usage = "";
SmallCircle::usage = "";
LongRightArrow::usage = "";
legalQ::usage = "";
simplify::usage = "";
eval::usage = "";


Begin["`Private`"]
(* Implementation of the package *)

toString//Clear
toString[s_String]:=s
toString[x_]:=ToString@x
toString[xs_List]:=toString/@xs
stringJoin//Clear
stringJoin[arg__]:=StringJoin@toString@arg
clear//ClearAll
clear~SetAttributes~HoldAll
clear[symbs__]:=(Clear@symbs;symbs)
(*domain//Clear
domain[func_]:=Cases[
DownValues@func/.a_Symbol\[RuleDelayed]Hold@a,
Hold[Pattern][_,arg_]\[RuleDelayed]arg,\[Infinity]]/.Hold[Blank]\[Rule]Sequence//ReleaseHold//DeleteDuplicates*)
automaticValue//Clear
automaticValue[Automatic,autoVal_]:=autoVal
automaticValue[arg_,_]:=arg
funcArgPattern//Clear
funcArgPattern[func_]:=Cases[
DownValues[func]/. a_Symbol:>Hold[a]//.{
Hold[Condition][exp_,_]:>exp,\!\(\*
TagBox[
StyleBox[
RowBox[{"\n", 
RowBox[{
RowBox[{"Hold", "[", "PatternTest", "]"}], "[", 
RowBox[{"exp_", ",", "_"}], "]"}]}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\):>exp,
Hold[Optional][exp_,_]:>exp
},Hold[RuleDelayed][Hold[HoldPattern][_[lhs__]],_]:>{lhs},
\[Infinity]]/. Hold[Pattern][_,Hold[Blank][obj_]]:>obj//ReleaseHold//Sort
funcTopHeads//Clear
funcTopHeads[func_]:=Cases[DownValues@func,
RuleDelayed[_,constructor_@___]:>constructor]//Union

(* ::Section:: *)
(* Region Title *)
composable // Clear
composable[_ar\[SmallCircle]_ar] = True;
NA // Unprotect;
NA // ClearAll
(*NA~Format~TraditionalForm="n/a";*)
NA // Protect;
objQ // Clear
objQ[arg : (_ct | _ob | _ar | _fr | _nt | _fn)] := 
 MatchQ[arg, _[_Association]]
objQ[_ctSymbol] = True;
objQ[args_List] := And @@ (objQ /@ args)
objQ[_] = False;
CenterDot // ClearAll
CenterDot~SetAttributes~HoldRest
CenterDot[ctSymbol[symbol_], "ct"] := getCt[ctSymbol@symbol]
CenterDot[ctSymbol[symbol_], ct] := getCt[ctSymbol@symbol]
CenterDot[ctSymbol[symbol_], arg_] := 
 getCt[ctSymbol@symbol]\[CenterDot]arg
CenterDot[objHead_[ass_Association], prop_String] /; 
  objQ@objHead[ass] := ass@prop
(*CenterDot[objHead_[ass_Association],"ass"]/;objQ@objHead[ass]:=ass*)


CenterDot[obj_?objQ, prop_] := 
 CenterDot[obj, #] &@ToString@Unevaluated@prop
CenterDot[obj_?objQ, props_List] := 
 Hold /@ Unevaluated@props /. Hold@prop_ :> CenterDot[obj, prop]
CenterDot[objs_List?objQ, prop_] := CenterDot[#, prop] & /@ objs
CenterDot[objs_List?objQ, props_List] := CenterDot[#, props] & /@ objs
CenterDot[obj_?objQ, prop_, props__] := 
 CenterDot[CenterDot[obj, prop], props]
CenterDot[ConditionalExpression[objs_?objQ, cond_], props__] := 
 ConditionalExpression[CenterDot[objs, props], cond]
setCt // Clear
setCt[ctSym_ctSymbol, C_ct] := (AppendTo[$ctDatabase, ctSym -> C]; 
  ctSym)
getCt // Clear
getCt[ctSym_ctSymbol] := Lookup[$ctDatabase, ctSym, $Failed]
getCt[] := Lookup[$ctDatabase, $workingCat, $Failed]
ctSymbol // Clear
ctSymbol[symbol_]@"ct" := getCt[ctSymbol@symbol]
ctSymbol[symbol_]@arg_ := getCt[ctSymbol@symbol]@arg
(*ctSymbol[symbol_]@"ct":=getCt[ctSymbol@symbol]
ctSymbol[symbol_]@arg_:=getCt[ctSymbol@symbol]\[CenterDot]arg*)
(*unknown//ClearAll
unknown::usage="Unknown entity which enable not-fully difined object \
to compute.";
unknown/:\[Not]unknown=unknown;
unknown/:unknown\[And]unknown=unknown;
unknown/:unknown\[And]True=unknown;
unknown/:True\[And]unknown=unknown;
unknown/:unknown\[And]False=False;
unknown/:False\[And]unknown=False;
unknown/:unknown\[Or]unknown=unknown;
unknown/:unknown\[Or]True=True;
unknown/:True\[Or]unknown=True;
unknown/:unknown\[Or]False=unknown;
unknown/:False\[Or]unknown=unknown;
unknown/:Equal[unknown,unknown]=unknown;
unknown/:Equal[lhs___,unknown,rhs___]:=unknown\[And]Equal[lhs,rhs]
unknownQ//Clear
unknownQ[unknown]=True;
unknownQ[_]=False;*)
(*category*)
ct // ClearAll
(*ct[ass_Association]@"ass":=ass*)
ct[ass_Association]@property_String := ass@property
(*ct[ass_Association]//Format:=ass@"label"*)
Ct // ClearAll
Ct // Options = {"label" -> Automatic, "evalable" -> True, 
   "obQ" -> Automatic, "arQ" -> Automatic, "dcQ" -> Automatic, 
   "composableQ" -> Automatic, "composeFunc" -> Automatic, 
   "composeFuncWithArgs" -> Automatic(*,"obConstructor"\[Rule]setMake,
   "obHead"\[Rule]set*)};
Ct::wrongDomainObQ = "Domain of '`1`' must be '_ob', not `2`";
Ct::wrongDomainArQ = "Domain of '`1`' must be '_ar', not `2`";
Ct::wrongArgPatternDcQ = 
  "Arg. pattern of '`1`' must be \
'_ar\[Colon]_ob\[LongRightArrow]_ob', not `2`";
Ct::wrongArgPatternComposableQ = 
  "Arg. pattern of func. 'composableQ' must be \
'_ar\[SmallCircle]_ar', not `1`";
Ct::wrongArgPatternComposeFunc = 
  "Arg. pattern of '`1`' must be '_ar\[SmallCircle]_ar', not `2`";
Ct::wrongArgPatternComposeFuncWithArgs = 
  "Arg. pattern of '`1`' must be '_ar\[SmallCircle]_ar[__]', not `2`";
Ct[_, OptionsPattern[]] := 
 Message[Ct::wrongArgPatternComposableQ, OptionValue@"composableQ"] /;
   funcArgPattern@
     OptionValue@"composableQ" =!= {{ar\[SmallCircle]ar}} \[And] 
   OptionValue@"composableQ" =!= Automatic
Ct[_, OptionsPattern[]] := 
 Message[Ct::wrongArgPatternComposeFunc, OptionValue@"composeFunc", 
   funcArgPattern@OptionValue@"composeFunc"] /; 
  funcArgPattern@
     OptionValue@"composeFunc" =!= {{ar\[SmallCircle]ar}} \[And] 
   OptionValue@"composeFunc" =!= Automatic
Ct[_, OptionsPattern[]] := 
 Message[Ct::wrongArgPatternComposeFuncWithArgs, 
   OptionValue@"composeFuncWithArgs", 
   funcArgPattern@OptionValue@"composeFuncWithArgs"] /; \[Not] 
    MatchQ[funcArgPattern@
      OptionValue@
       "composeFuncWithArgs", {{ar\[SmallCircle]ar[__]}}] \[And] 
   OptionValue@"composeFuncWithArgs" =!= Automatic
Ct[_, OptionsPattern[]] := 
 Message[Ct::wrongArgPatternDcQ, OptionValue@"dcQ", 
   funcArgPattern@OptionValue@"dcQ"] /; 
  funcArgPattern@
     OptionValue@
      "dcQ" =!= {{ar \[Colon] ob\[LongRightArrow]ob}} \[And] 
   OptionValue@"dcQ" =!= Automatic
Ct[_, OptionsPattern[]] := 
 Message[Ct::wrongDomainObQ, OptionValue@"obQ", 
   funcArgPattern@OptionValue@"obQ"] /; 
  funcArgPattern@OptionValue@"obQ" =!= {{ob}} \[And] 
   OptionValue@"obQ" =!= Automatic
Ct[_, OptionsPattern[]] := 
 Message[Ct::wrongDomainArQ, OptionValue@"arQ", 
   funcArgPattern@OptionValue@"arQ"] /; 
  funcArgPattern@OptionValue@"arQ" =!= {{ar}} \[And] 
   OptionValue@"arQ" =!= Automatic
Ct[symbol_, OptionsPattern[]] := 
 setCt[ctSymbol@symbol, 
  ct@Association[(*"ctSymbol"\[Rule]ctSymbol@symbol,*)
    "obQ" -> automaticValue[OptionValue@"obQ", Fn@symbol@"obQ"], 
    "arQ" -> automaticValue[OptionValue@"arQ", Fn@symbol@"arQ"], 
    "dcQ" -> automaticValue[OptionValue@"dcQ", Fn@symbol@"dcQ"],
    "composableQ" -> 
     automaticValue[OptionValue@"composableQ", composable], 
    "composeFunc" -> 
     automaticValue[OptionValue@"composeFunc", 
      Fn@symbol@"composeFunc"], 
    "composeFuncWithArgs" -> 
     automaticValue[OptionValue@"composeFuncWithArgs", 
      Fn@symbol@"composeFuncWithArgs"],
    "evalable" -> OptionValue@"evalable",
    (*"obConstructor"\[Rule]OptionValue@"obConstructor",
    "obHead"\[Rule]OptionValue@"obHead",*)
    "label" -> 
     automaticValue[OptionValue@"label", ToString@symbol]]
  ]
(*Object*)
ob // ClearAll
(*ob[ass_Association]@"ass":=ass*)
ob[ass_Association]@property_String := ass@property
ob[ass_Association]~Format~TraditionalForm := ass@"label"
Ob // ClearAll
Ob // Options = {"label" -> Automatic};
(*Ob[A:Except@_ctSymbol,OptionsPattern[]]:=ob@<|"object"\[Rule]$\
workingCat["obConstructor"]@A(*\[Piecewise] A   \
Head@A===$workingCat@"obHead"
$workingCat["obConstructor"]@A  True



*),"ct"\[Rule]$workingCat,"label"\[Rule]automaticValue[OptionValue@\
"label",A]|>
Ob[A:Except@_ctSymbol,C_ctSymbol,OptionsPattern[]]:=ob@<|"object"\
\[Rule]C["obConstructor"]@A(*\[Piecewise]   A   Head@A===C@"obHead"
C["obConstructor"]@A    True



*),"ct"\[Rule]C,"label"\[Rule]automaticValue[OptionValue@"label",A]|>*)


Ob[A : Except@_ctSymbol, OptionsPattern[]] := 
 ob@Association["object" -> A, "ct" -> $workingCat, 
   "label" -> automaticValue[OptionValue@"label", A]]
Ob[A : Except@_ctSymbol, C_ctSymbol, OptionsPattern[]] := 
 ob@Association["object" -> A, "ct" -> C, 
   "label" -> automaticValue[OptionValue@"label", A]]
(*Simple Type System*)
comprehension // ClearAll
comprehension~SetAttributes~HoldAll
dom // Clear
cod // Clear
fn // ClearAll
(*fn[ass_Association]@"ass":=ass*)
fn[ass_Association]@property_String := ass@property
fn[ass_Association]~Format~TraditionalForm := {ass@"function", "::", 
  ass@"dom" \[DirectedEdge] ass@"cod"}
Fn // ClearAll
Fn // Options = {"label" -> Automatic};
(*Fn[symbol_,opts___Rule]:=Fn[{dom@#,cod@#},#,opts]&@symbol@\
"function"*)
(*Fn[{},function_,opts___Rule]:=Fn[{NA,NA},function,opts]*)
Fn[{NA, NA}, _, OptionsPattern[]] := Message[Fn::tooambiguousdc]
Fn::tooambiguousdc = 
  "At least either domain or codomain must be specified.";
Fn[{NA, cod_}, function_, opts___Rule] := 
 Module[{x}, 
  Fn[{comprehension[x, function@x \[Element] cod], cod}, function, 
   opts]]
Fn[{dom_, NA}, function_, opts___Rule] := 
 Module[{x}, 
  Fn[{dom, comprehension[function@x, x \[Element] dom]}, function, 
   opts]]
(*Fn[{dom_, cod_}, function_, OptionsPattern[]] := 
 fn@Association["dom" -> dom, "cod" -> cod, "function" -> function, 
   "label" -> "func"]*)
Fn[{dom_, cod_}, function_, OptionsPattern[]] := 
 fn@Association["dom" -> dom, "cod" -> cod, "function" -> function, 
   "label" -> automaticValue[OptionValue@"label", function]]

(*arrow*)
ar // ClearAll
(*ar[ass_Association]@"ass":=ass*)
ar[ass_Association]@property_String := ass@property
ar[ass_Association]~Format~
  TraditionalForm := {ass["fn"]@"function" \[Colon] 
   ass["dom"] \[DirectedEdge] ass["cod"]}
Ar // ClearAll
Ar // Options = {"label" -> Automatic};
Ar[symbol_: Except@_ctSymbol, opts___Rule] := 
 Ar[{Ob@dom@symbol, Ob@cod@symbol}, Fn@symbol@"fn", opts]
Ar[symbol_: Except@_ctSymbol, C_ctSymbol, opts___Rule] := 
 Ar[{Ob[dom@symbol, C], Ob[cod@symbol, C]}, C, Fn@symbol@"fn", opts]
Ar[{dom_ob, cod_ob}, fn_fn, opts___Rule] := 
 Ar[{dom, cod}, fn, $workingCat, opts]
Ar[{dom_ob, cod_ob}, _fn, \[DoubleStruckCapitalC]_ctSymbol, 
   OptionsPattern[]] /; \[Not] (dom\[CenterDot]"ct" == 
     cod\[CenterDot]"ct" == \[DoubleStruckCapitalC]) := 
 Message[Ar::unsameCt, dom\[CenterDot]"ct", 
  cod\[CenterDot]"ct", \[DoubleStruckCapitalC]]
Ar::unsameCt = 
  "The ct of domain:'`1`', codomain'`2`', and of this arrow '`1`'  \
must be the same.";
Ar[{dom_ob, cod_ob}, fn_fn, \[DoubleStruckCapitalC]_ctSymbol, 
  OptionsPattern[]] :=
 ConditionalExpression[
  ar@Association["dom" -> dom, "cod" -> cod, "fn" -> fn, 
    "ct" -> \[DoubleStruckCapitalC], 
    "label" -> 
     automaticValue[OptionValue@"label", 
      dom@"label" \[DirectedEdge] cod@"label"]], (dom\[CenterDot]"object" == 
      fn\[CenterDot]"dom" \[And] 
     cod\[CenterDot]"object" == fn\[CenterDot]"cod") \[Or] ((*areIn*)
    SubsetEqual[dom\[CenterDot]"object", 
      fn\[CenterDot]"dom"] \[And](*areIn*)
     SubsetEqual[cod\[CenterDot]"object", fn\[CenterDot]"cod"])]
(*Functor*)
fr // ClearAll
(*fr[ass_Association]@"ass":=ass*)
fr[ass_Association]@property_String := ass@property
fr[ass_Association]~Format~TraditionalForm := ass@"label"
Fr // ClearAll
Fr // Options = {"label" -> Automatic};
Fr[symbol_Symbol, opts___Rule] := 
 Fr[{ctSymbol@symbol@"dom", ctSymbol@symbol@"cod"}, {Fn@symbol@"fnOb",
    Fn@symbol@"fnAr"}, opts]
Fr[{dom_ctSymbol, cod_ctSymbol}, {fnOb_fn, fnAr_fn}, 
  OptionsPattern[]] := 
 fr@Association["dom" -> dom, "cod" -> cod, "fnOb" -> fnOb, "fnAr" -> fnAr, 
   "label" -> 
    automaticValue[OptionValue@"label", 
     dom@"label" \[DirectedEdge] cod@"label"]]
(* Natural Transformation *)
nt // ClearAll
(*nt[ass_Association]@"ass":=ass*)
nt[ass_Association]@property_String := ass@property
nt[ass_Association]~Format~TraditionalForm := ass@"label"
Nt // ClearAll
Nt // Options = {"label" -> Automatic};
Nt[symbol_(*Symbol*), opts___Rule] := 
 Nt[{Fr@symbol@"dom", Fr@symbol@"cod"}, Fn@symbol@"fn", opts]
Nt[{dom_fr, cod_fr}, fn_fn, OptionsPattern[]] := 
 nt@Association["dom" -> dom, "cod" -> cod, "fn" -> fn, 
   "label" -> 
    automaticValue[OptionValue@"label", 
     dom@"label" \[DirectedEdge] cod@"label"]]
power // Clear
(*power[x_,y_]//Format:=Superscript[x@"label",y@"label"]*)
ctSymbol /: Equal[syms__ctSymbol] := SameQ @@ (First /@ {syms})
ctSymbol /: 
 Equal[lhs___, sym_ctSymbol, rhs___] /; 
  Count[{lhs, sym, rhs}, _ctSymbol] >= 2 := 
 Equal[#@True] \[And] Equal[sym, #@False] &@
  GroupBy[{lhs, sym, rhs}, MatchQ[#, _ctSymbol] &, 
   Apply@Sequence](*@*Key*)
ob /: Equal[As__ob] := 
 And @@ (Equal @@ ({As} /. A_ob :> A@#) & /@ {"object", "ct"})
ob /: Equal[lhs___, A_ob, rhs___] /; Count[{lhs, A, rhs}, _ob] >= 2 :=
  Equal[#@True] \[And] Equal[A, #@False] &@
  GroupBy[{lhs, A, rhs}, MatchQ[#, _ob] &, Apply@Sequence](*@*Key*)
ar /: Equal[fs__ar] := 
 And @@ (Equal @@ ({fs} /. f_ar :> f@#) & /@ {"dom", "cod", "fn", 
     "ct"})
ar /: Equal[lhs___, f_ar, rhs___] /; Count[{lhs, f, rhs}, _ar] >= 2 :=
  Equal[#@True] \[And] Equal[f, #@False] &@
  GroupBy[{lhs, f, rhs}, MatchQ[#, _ar] &, Apply@Sequence](*@*Key*)

(*ct/:Equal[Cs__ct]:=Equal@@(#@"ctSymbol"&/@{Cs})
ct/:Equal[lhs___,C_ct,rhs___]/;Count[{lhs,C,rhs},_ct]\[GreaterEqual]2:=\
Equal[#@True]\[And]Equal[C,#@False]&@GroupBy[{lhs,C,rhs},MatchQ[#,_ct]\
&,Apply@Sequence]@*Key*)
$ctDatabase = Association[];
$workingCat = Ct[SetCat];

(* ::Section:: *)
(* Region Title *)

SmallCircle // ClearAll
SmallCircle[f_ar] := f
SmallCircle~SetAttributes~{Flat, OneIdentity};
LongRightArrow // ClearAll
LongRightArrow[A_ob] := A
LongRightArrow~SetAttributes~{Flat, OneIdentity};
legalQ // Clear
legalQ[A_ob] := (A\[CenterDot]"ct"\[CenterDot]"obQ")@A
legalQ[f_ar] := (f\[CenterDot]"ct"\[CenterDot]"arQ")@f
legalQ[g_ar\[SmallCircle]f_ar, "sameCt"] := 
 g\[CenterDot]"ct" == f \[CenterDot]"ct"
legalQ[g_ar\[SmallCircle]f_ar, "dc"] := 
 g\[CenterDot]"dom" == f\[CenterDot]"cod"
legalQ[g_ar\[SmallCircle]f_ar, 
  "composableQ"] := (f\[CenterDot]"ct"\[CenterDot]"composableQ")[
  g\[SmallCircle]f]
legalQ[g_ar\[SmallCircle]f_ar] := 
 If[legalQ[g\[SmallCircle]f, "sameCt"] \[And] 
   legalQ[g\[SmallCircle]f, "dc"], 
  legalQ[g\[SmallCircle]f, "composableQ"], False]
legalQ[SmallCircle[g_ar, f_ar, fs__ar], 
  PatternSequence[arg_String] | PatternSequence[]] := 
 legalQ[g\[SmallCircle]f, arg] \[And] legalQ[SmallCircle[f, fs], arg]
legalQ[f_ar \[Colon] A_ob\[LongRightArrow]B_ob, "sameCt"] := 
 Equal @@ ({f, A, B}\[CenterDot]"ct")
legalQ[f_ar \[Colon] A_ob\[LongRightArrow]B_ob] := 
 legalQ[f \[Colon] A\[LongRightArrow]B, 
   "sameCt"] \[And] (f\[CenterDot]"ct"\[CenterDot]"dcQ")[
   f \[Colon] A\[LongRightArrow]B]
legalQ[SmallCircle[gs___ar, g_ar, f_ar] \[Colon] 
   LongRightArrow[A_ob, B_ob, Cs___ob]] := 
 legalQ[g\[SmallCircle]f] \[And] 
  legalQ[f \[Colon] A\[LongRightArrow]B] \[And] 
  legalQ[SmallCircle[gs, g] \[Colon] LongRightArrow[B, Cs]]
(*legalQ[f_ar[A_ob]]:=areIn[A\[CenterDot]"object",f\[CenterDot]"dom"\
\[CenterDot]"object"]\[And]Equal@@({f,A}\[CenterDot]"ct")*)
legalQ[f_ar[A_ob]] := 
 A\[CenterDot]"object" \[SubsetEqual] 
   f\[CenterDot]"dom"\[CenterDot]"object" \[And] 
  Equal @@ ({f, A}\[CenterDot]"ct")
simplify // ClearAll
simplify[f_ar\[SmallCircle]g_ar] := 
 If[legalQ[f\[SmallCircle]g], 
  Ar[{g\[CenterDot]"dom", f\[CenterDot]"cod"}, 
   Fn[{g\[CenterDot]"dom", 
     f\[CenterDot]"cod"}, (f\[CenterDot]"ct"\[CenterDot]"composeFunc")[
     f\[SmallCircle]g]], f\[CenterDot]"ct"], False]
simplify[SmallCircle[f_ar, g_ar, gs__ar]] := 
 If[legalQ[f\[SmallCircle]g], 
  simplify@SmallCircle[simplify[f\[SmallCircle]g], gs], False]
simplify[f_ar\[SmallCircle]g_ar[args__]] := 
 ConditionalExpression[(f\[CenterDot]"ct"\[CenterDot]\
"composeFuncWithArgs")[f\[SmallCircle]g[args]], 
  legalQ[f\[SmallCircle]g[args]]]
simplify[f_ar[A_ob]] := 
 If[legalQ[f[A]], 
  Ob[(f\[CenterDot]"fn"\[CenterDot]"function")@(A\[CenterDot]"object"), 
   f\[CenterDot]"ct"], False]
simplify[f_ar[A_ob]] /; \[Not] f\[CenterDot]"ct"\[CenterDot]"evalable" := 
 If[legalQ[f[A]], f[A], False]
(*simplify[func_fn[A_ob]]:=If[legalQ[func[A]],Ob[(func\[CenterDot]\
"function")@(A\[CenterDot]"object"),func\[CenterDot]"cod"],False]*)
simplify[F_fr[A_ob]] := 
 Ob[(F\[CenterDot]"fnOb"\[CenterDot]"function")[A\[CenterDot]"object"], 
  F\[CenterDot]"cod"]
(*simplify[F_fr[f_ar]]:=Ar[(F\[CenterDot]"fnAr"\[CenterDot]"function")[f\
\[CenterDot]"object"],F\[CenterDot]"cod"]*)
(*simplify[F_fr[f_ar]]:=Ar[{Ob[dom@#,F\[CenterDot]"cod"],Ob[cod@#,F\
\[CenterDot]"cod"]},Fn[{dom@#,cod@#},#],F\[CenterDot]"cod"]&[(F\
\[CenterDot]"fnAr"\[CenterDot]"function")[f\[CenterDot]"fn"\[CenterDot]\
"function"]]*)
simplify[F_fr[f_ar]] := 
 Ar[#, Fn[#\[CenterDot]"object", \
(F\[CenterDot]"fnAr"\[CenterDot]"function")[
      f\[CenterDot]"fn"\[CenterDot]"function"]], F\[CenterDot]"cod"] &[
  F\[CenterDot]"fnAr"\[CenterDot]"cod"\[CenterDot]"object" /. 
   power[A_, B_] :> {B, A}]
(*"TODO:FIXME"*)
legalQ[F_fr[f_ar]] := "FIXME"
(*simplify[A_ob~areIn~B_ob]:=Equal@@({A,B}\[CenterDot]"ct")\[And]areIn[\
A\[CenterDot]"object",B\[CenterDot]"object"]*)
simplify[A_ob \[SubsetEqual] B_ob] := 
 Equal @@ ({A, B}\[CenterDot]"ct") \[And] 
  A\[CenterDot]"object" \[SubsetEqual] B\[CenterDot]"object"
simplify[{xs__} \[SubsetEqual] 
   range : (Integers | Reals | Complexes)] := {xs} \[Element] range
simplify[{xs__} \[SubsetEqual] region_?RegionQ] := 
 And @@ RegionMember[region, xs]
(*simplify[{xs___}\[SubsetEqual]{ys___}]:=And@@(Or@@@Outer[Equal,{xs},\
{ys}])*)
(*simplify[dom[exp_]~areIn~dom[exp_]]=True;
simplify[cod[exp_]~areIn~cod[exp_]]=True;*)
simplify[dom[exp_] \[SubsetEqual] dom[exp_]] = True;
simplify[cod[exp_] \[SubsetEqual] cod[exp_]] = True;
simplify[x_ \[SubsetEqual] x_] = True;


(* ::Section:: *)
(* Region Title *)

eval // Clear
eval[expr_, "fn"] := expr //. {
   fn_fn[ob_ob] :> fn["function"][ob["object"]],
   fn_fn[ar_ar] :> fn["function"][ar["fn"]["function"]]}
eval[expr_, "fr"] := expr //. {
   fr_fr[ob_ob] :> Ob[fr["fnOb"]@ob // eval[#, "fr"] &, fr["cod"]],
   fr_fr[ar_ar] :> 
    Ar[Reverse~Composition~List @@ fr["fnAr"]["cod"]["object"], 
     Fn[Reverse~Composition~List @@ fr["fnAr"]["cod"]["object"], 
      fr["fnAr"]@ar // eval[#, "fr"] &], fr["cod"]]}
eval[expr_, "ar"] := expr //. {
   ar_ar[ob_ob](*/;ar["ct"]===ob["ct"]*):> 
    Ob[ar["fn"]["function"][ob["object"]], ar["ct"]]}
eval[expr_, "nt"] := expr //. {
   nt_nt[ob_ob] :> 
    Ob[nt["fn"]@ob // eval[#, "fn"] &, nt["cod"]["cod"](*==nt["dom"][
     "cod"]*)]}

End[]

EndPackage[]

