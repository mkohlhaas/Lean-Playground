/- ====================== -/
/- Evaluating Expressions -/
/- ====================== -/

-- https://lean-lang.org/functional_programming_in_lean/Getting-to-Know-Lean/Evaluating-Expressions/#evaluating

-- Lean 4 is a strict language!

#eval 1 + 2                                                  
#eval 1 + 2 * 5                                              
#eval 1 + 3 * 5                                              
#eval String.append "Hello, " "Lean!"                        
#eval String.append "great " (String.append "oak " "tree")   
#eval String.append "great " $ String.append "oak " "tree"   
#eval String.append "it is " (if 1 > 2 then "yes" else "no") 

#eval 2^32                                                   
#eval 2^(2 * 32)                                             
#eval 2^(4 * 32)                                             
#eval 2^(8 * 32)                                             

#check 2^32                                                  
#check 2^(2 * 32)                                            
#check 2^(4 * 32)                                            
#check 2^(8 * 32)                                            

/- --------------------- -/
/- Messages You May Meet -/
/- --------------------- -/

-- https://lean-lang.org/functional_programming_in_lean/Getting-to-Know-Lean/Evaluating-Expressions/#evaluating-messages

-- functions cannot be displayed
#eval  String.append "it is "                                
#check String.append "it is "                                

/- --------- -/
/- Exercises -/
/- --------- -/

-- https://lean-lang.org/functional_programming_in_lean/find/?domain=Verso.Genre.Manual.section&name=evaluating-exercises

#eval 42 + 19                                                
#eval String.append "A" (String.append "B" "C")              
#eval String.append "A" $ String.append "B" "C"              
#eval String.append (String.append "A" "B") "C"              
#eval if 3 == 3 then 5 else 7                                
#eval if 3 == 4 then "equal" else "not equal"                
