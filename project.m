$axioms = True;
$substitutionCount = 0;

getAxiom[axiom_] := ToString[axiom[[2]]]

getGoal[goal_] := ToString[goal[[2]]]

getSubstitution[substitution_] := Module[{newSubstitution},
  newSubstitution = ToString[substitution[[2]]];
  newSubstitution = 
   Nest[Function[# <> " "], newSubstitution, $substitutionCount];
  $substitutionCount += 1;
  newSubstitution
  ]

getSubstitutionSide[substitution_] := 
 substitution[[5]] /; IntegerQ[substitution[[5]]]
getSubstitutionSide[substitution_] := 
 substitution[[4]] /; ! IntegerQ[substitution[[5]]]

getSubstitutionOutputSubpart[substitution_] := 
 ToString[substitution[[6, 3, 3]]] /; IntegerQ[substitution[[5]]]
getSubstitutionOutputSubpart[substitution_] := 
 ToString[substitution[[5, 3, 3]]] /; ! IntegerQ[substitution[[5]]]

getSubstitutionSubpartNumber[substitution_] := 
 Flatten[Position[(ToExpression[
      getSubstitutionOutput[substitution]])[[
    getSubstitutionSide[substitution]]], 
   ToExpression[getSubstitutionOutputSubpart[substitution]]]]

getSubstitutionInputSubpart[substitution_] := 
 ToString[(ToExpression[getSubstitutionInput[substitution]])[[
    getSubstitutionSide[substitution]]]] /; 
  Length[getSubstitutionSubpartNumber[substitution]] == 0
getSubstitutionInputSubpart[substitution_] := 
 ToString[(ToExpression[getSubstitutionInput[substitution]])[[
    getSubstitutionSide[substitution], 
    First[getSubstitutionSubpartNumber[substitution]]]]] /; 
  Length[getSubstitutionSubpartNumber[substitution]] != 0

getSubstitutionOutput[substitution_] := 
 ToString[substitution[[6, 2]]] /; IntegerQ[substitution[[5]]]
getSubstitutionOutput[substitution_] := 
 ToString[substitution[[5, 2]]] /; ! IntegerQ[substitution[[5]]]

getSubstitutionInput[substitution_] := 
 getStep[getSubstitutionInputNumber[substitution]]

getSubstitutionInputNumber[substitution_] := 
 substitution[[6, 3, 1]] /; IntegerQ[substitution[[5]]]
getSubstitutionInputNumber[substitution_] := 
 substitution[[5, 3, 1]] /; ! IntegerQ[substitution[[5]]]

getSubstitutionJustification[substitution_] := 
 getStep[substitution[[6, 3, 4]]] /; IntegerQ[substitution[[5]]]
getSubstitutionJustification[substitution_] := 
 getStep[substitution[[5, 3, 4]]] /; ! IntegerQ[substitution[[5]]]

getSubstitutionJustificationFull[substitution_] := 
 getStepFull[substitution[[6, 3, 4]]] /; IntegerQ[substitution[[5]]]
getSubstitutionJustificationFull[substitution_] := 
 getStepFull[substitution[[5, 3, 4]]] /; ! IntegerQ[substitution[[5]]]

getJustification[justification_] := 
 getStep[getJustificationNumber[justification]]

getJustificationNumber[justification_] := justification[[3, 1]]

getStepNumber[step_] := ToString[step[[1]]]

getStep[stepNumber_Integer] := 
 getAxiom[getStepFull[stepNumber]] /; 
  getStepType[getStepFull[stepNumber]] == axiom
getStep[stepNumber_Integer] := 
 getGoal[getStepFull[stepNumber]] /; 
  getStepType[getStepFull[stepNumber]] == goal
getStep[stepNumber_Integer] := 
 getSubstitutionOutput[getStepFull[stepNumber]] /; 
  getStepType[getStepFull[stepNumber]] == substitution
getStep[stepNumber_Integer] := 
 getJustification[getStepFull[stepNumber]] /; 
  getStepType[getStepFull[stepNumber]] == justification

getStepFull[stepNumber_Integer] := 
 Select[$proofList, #[[1]] == stepNumber &][[1]]

getStepType[step_] := axiom /; step[[0]] == InitialLemma
getStepType[step_] := goal /; step[[0]] == InitialHypothesis
getStepType[step_] := substitution /; step[[0]] == ApplyLemma
getStepType[step_] := 
 justification /; (step[[0]] == OrientRule || 
    step[[0]] == SelectEquation || step[[0]] == CriticalPairLemma || 
    step[[0]] == InstanceConstant2)
getStepType[step_] := conclusion /; step[[0]] == FinalGoal

texify[step_] := 
 StringReplace[
  step, {"_" -> "\_", "==" -> "=", "->" -> "\\to", "[" -> "(", 
   "]" -> ")"}]

addToProofCheck[step_, check_String] := 
 check <> "s" <> getStepNumber[step] <> "=" <> getAxiom[step] <> 
   ";\n" /; getStepType[step] == axiom
addToProofCheck[step_, check_String] := 
 check <> "s" <> getStepNumber[step] <> "=" <> getGoal[step] <> 
   ";\n" /; getStepType[step] == goal
addToProofCheck[step_, check_String] := (
   If[getSubstitutionOutput[step] == "True",
    check <> "s" <> getStepNumber[step] <> "=MapAt[ReplaceAll[" <> 
     getSubstitution[step] <> "],s" <> 
     ToString[getSubstitutionInputNumber[step]] <> "," <> 
     ToString[getSubstitutionSide[step]] <> "]"
    , If[Length[getSubstitutionSubpartNumber[step]] == 0,
     check <> "s" <> getStepNumber[step] <> "=MapAt[Replace[" <> 
      getSubstitution[step] <> "],s" <> 
      ToString[getSubstitutionInputNumber[step]] <> "," <> 
      ToString[getSubstitutionSide[step]] <> "];\n"
     , check <> "s" <> getStepNumber[step] <> "=MapAt[Replace[" <> 
      getSubstitution[step] <> "],s" <> 
      ToString[getSubstitutionInputNumber[step]] <> ",{" <> 
      ToString[getSubstitutionSide[step]] <> "," <> 
      ToString[First[getSubstitutionSubpartNumber[step]]] <> "}];\n"
     ]
    ]
   ) /; getStepType[step] == substitution
addToProofCheck[step_, check_String] := 
 check /; (getStepType[step] == justification || 
    getStepType[step] == conclusion)

addToProof[step_, proof_String] := 
 proof <> "\\begin{axiom}\nWe are given that:\n\\begin{equation}\n" <>
    texify[getAxiom[step]] <> ".\n\\end{equation}\n\\end{axiom}\n" /; 
  getStepType[step] == axiom
addToProof[step_, proof_String] := 
 proof <> "\\begin{theorem}\nWe would like to show that:\n\
\\begin{equation}\n" <> texify[getGoal[step]] <> 
   ".\n\\end{equation}\n\\end{theorem}\n\\section{Key Results}\n" /; 
  getStepType[step] == goal
addToProof[step_, proof_String] := (
   If[getSubstitutionOutput[step] == "True",
    proof <> 
     "\\section{Proof of Main Result}\n\\begin{proof}\nFinally, \
applying the substitution:\n\\begin{equation}\n"
     <> texify[getSubstitution[step]]
     <> "\n\\end{equation}\nto the expression:\n\\begin{equation}\n"
     <> texify[getSubstitutionInput[step]]
     <> "\n\\end{equation}\nyields the required result. This \
substitution follows from the fact that:\n\\begin{equation}\n"
     <> texify[getSubstitutionJustification[step]]
     <> "\n\\end{equation}\n\\end{proof}\n"
    , proof <> 
     "\\begin{lemma}\nIt can be shown that:\n\\begin{equation}\n"
     <> texify[getSubstitutionOutput[step]]
     <> "\n\\end{equation}\n\\end{lemma}\n\\begin{proof}\nWe apply \
the substitution:\n\\begin{equation}\n"
     <> texify[getSubstitution[step]]
     <> "\n\\end{equation}\nto the term ${"
     <> texify[getSubstitutionInputSubpart[step]]
     <> "}$ in the expression:\n\\begin{equation}\n"
     <> texify[getSubstitutionInput[step]]
     <> "\n\\end{equation}\nto obtain the term ${"
     <> texify[getSubstitutionOutputSubpart[step]]
     <> "}$:\n\\begin{equation}\n"
     <> texify[getSubstitutionOutput[step]]
     <> ".\n\\end{equation}\nThis substitution follows from the fact \
that:\n\\begin{equation}\n"
     <> texify[getSubstitutionJustification[step]]
     <> ".\n\\end{equation}\n\\end{proof}\n"]
   ) /; getStepType[step] == substitution
addToProof[step_, proof_String] := 
 proof /; (getStepType[step] == justification || 
    getStepType[step] == conclusion)

addToStepList[step_, stepList_List] := 
 Append[stepList, getAxiom[step]] /; getStepType[step] == axiom
addToStepList[step_, stepList_List] := 
 Append[stepList, getGoal[step]] /; getStepType[step] == goal
addToStepList[step_, stepList_List] := Module[{substitution},
   substitution = getSubstitution[step];
   Append[Append[stepList, substitution], 
    getSubstitutionOutput[step]]
   ] /; getStepType[step] == substitution
addToStepList[step_, stepList_List] := 
 Append[stepList, "True"] /; getStepType[step] == conclusion
addToStepList[step_, stepList_List] := 
 stepList /; getStepType[step] == justification

addToStepColours[step_, stepColours_List] := 
 Append[stepColours, getAxiom[step] -> Red] /; 
  getStepType[step] == axiom
addToStepColours[step_, stepColours_List] := 
 Append[stepColours, getGoal[step] -> Green] /; 
  getStepType[step] == goal
addToStepColours[step_, stepColours_List] := Module[{substitution},
   substitution = getSubstitution[step];
   Append[stepColours, substitution -> Yellow]
   ] /; getStepType[step] == substitution
addToStepColours[step_, stepColours_List] := 
 Append[stepColours, "True" -> Black] /; 
  getStepType[step] == conclusion
addToStepColours[step_, stepColours_List] := 
 stepColours /; getStepType[step] == justification

addToStepConnections[step_, stepConnections_List] := 
 Module[{substitution},
   substitution = getSubstitution[step];
   Append[
    Append[Append[stepConnections, 
      DirectedEdge[getSubstitutionInput[step], substitution]], 
     DirectedEdge[substitution, getSubstitutionOutput[step]]], 
    DirectedEdge[getSubstitutionJustification[step], substitution]]
   ] /; getStepType[step] == substitution
addToStepConnections[step_, stepConnections_List] := 
 stepConnections /; (getStepType[step] == axiom || 
    getStepType[step] == goal || getStepType[step] == justification ||
     getStepType[step] == conclusion)

addToStepConnectionStyles[step_, stepConnectionStyles_List] := 
 Module[{substitution},
   substitution = getSubstitution[step];
   Append[
    stepConnectionStyles, (getSubstitutionJustification[step] -> 
       substitution) -> Dashed]
   ] /; getStepType[step] == substitution
addToStepConnectionStyles[step_, stepConnectionStyles_List] := 
 stepConnectionStyles /; (getStepType[step] == axiom || 
    getStepType[step] == goal || getStepType[step] == justification ||
     getStepType[step] == conclusion)

addAxiom[axiom_] := $axioms = And[axiom, $axioms]

clearAxioms[] := $axioms = True

prove[theorem_] := Module[{proof},
  proof = EquationalLogic`FindProof[theorem, $axioms][[1]];
  proof = 
   With[{vars = 
      Union[Cases[proof, 
        s_Symbol /; Context[s] === "Quantifier`", {0, Infinity}]]}, 
    ReplaceAll[proof, 
     Thread[vars -> 
       Table[Symbol["x" <> ToString[i]], {i, Length[vars]}]]]];
  Map[Function[$proofList = Append[$proofList, #]], proof];
  proof
  ]

proveTheorem[theorem_] := 
 Module[{proof, stepList = {}, stepColours = {}, stepConnections = {},
    stepConnectionStyles = {}},
  $proofList = {};
  proof = prove[theorem];
  $substitutionCount = 0;
  Map[Function[stepList = addToStepList[#, stepList]], $proofList];
  $substitutionCount = 0;
  Map[Function[
    stepColours = addToStepColours[#, stepColours]], $proofList];
  $substitutionCount = 0;
  Map[Function[
    stepConnections = 
     addToStepConnections[#, stepConnections]], $proofList];
  $substitutionCount = 0;
  Map[Function[
    stepConnectionStyles = 
     addToStepConnectionStyles[#, 
      stepConnectionStyles]], $proofList];
  Graph[stepList, stepConnections, VertexLabels -> Automatic, 
   VertexStyle -> stepColours, EdgeStyle -> stepConnectionStyles]
  ]

presentProof[theorem_] := Module[{proof, proofText = ""},
  $proofList = {};
  proofText = 
   "\\documentclass{article}\n\\usepackage{amsmath,amsthm,fullpage}\n\
\\newtheorem{theorem}{Theorem}\n\\newtheorem{axiom}{Axiom}\n\
\\newtheorem{lemma}{Lemma}\n\\begin{document}\n\\title{An \
Automatically Generated Proof}\n\\author{Wolfram Mathematica}\n\
\\maketitle\n\\section{Introduction}\n";
  proof = prove[theorem];
  Map[Function[proofText = addToProof[#, proofText]], $proofList];
  proofText = proofText <> "\\end{document}";
  Export["proof.tex", proofText, "Text"]
  ]

checkProof[theorem_] := Module[{proof, checkCode = ""},
  $proofList = {};
  proof = prove[theorem];
  checkCode = "Hold[";
  Map[Function[checkCode = addToProofCheck[#, checkCode]], $proofList];
  checkCode = checkCode <> "]";
  ToExpression[checkCode]
  ]