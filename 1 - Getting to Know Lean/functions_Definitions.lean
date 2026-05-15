/- ------------------------- -/
/- Functions and Definitions -/
/- ------------------------- -/

-- https://lean-lang.org/functional_programming_in_lean/find/?domain=Verso.Genre.Manual.section&name=functions-and-definitions

def hello         := "Hello"
def lean : String := "Lean"

#eval String.append hello lean                                  
#eval String.append " " lean                                    
#eval String.append hello (String.append " " lean)              
#eval String.append hello $ String.append " " lean              

/- ------------------ -/
/- Defining Functions -/
/- ------------------ -/

-- https://lean-lang.org/functional_programming_in_lean/find/?domain=Verso.Genre.Manual.section&name=defining-functions

#check (fun    => 42)                                           
#check (fun _  => 42)                                           
#check (fun () => 42)                                           

def add1_1  n              := n + 1
def add1_2 (n : Nat) : Nat := n + 1
def add1_3                 := (· + 1)

-- NOTE: little trick - treat it as an expression!
#check  add1_1                                                  
#check (add1_1)                                                 
#check @add1_1                                                  
#check @add1_3                                                  

#eval add1_1 5                                                  
#eval add1_1 7                                                  

#eval add1_2 5                                                  
#eval add1_2 7                                                  

#eval add1_3 5                                                  
#eval add1_3 7                                                  

def maximum1 n k :=
  if n < k                                                      
    then k
    else n
  
def maximum2 (n : Nat) (k : Nat) :=
  if n < k
    then k
    else n 

#check (maximum2)                                               
#check @maximum2                                                

#eval maximum2 2 5                                              
#eval maximum2 5 2                                              
#eval maximum2 (5 + 8) (2 * 7)                                  

-- can be written with -> and →
example : Nat -> Nat        := add1_1
example : Nat -> Nat -> Nat := maximum2
example : Nat →  Nat        := add1_1
example : Nat →  Nat →  Nat := maximum2

def spaceBetween'  before after :=
  String.append before $ String.append " " after

def spaceBetween'' before after : String :=                     
  String.append before $ String.append " " after

def spaceBetween''' (before : String) (after : String) :=
  String.append before $ String.append " " after
  
def spaceBetween (before : String) (after : String) :=
  before ++ " " ++ after

#eval spaceBetween "Hans" "Schmid"                              
  
-- currying
#check @spaceBetween                                                  
#check @spaceBetween ""                                            
#check @spaceBetween "" ""                                      

-- Function arrows associate to the right, which means that Nat → Nat → Nat
-- should be parenthesized Nat → (Nat → Nat).

/- --------- -/
/- Exercises -/
/- --------- -/

-- https://lean-lang.org/functional_programming_in_lean/find/?domain=Verso.Genre.Manual.section&name=function-definition-exercises

-- Define the function joinStringsWith with type String → String → String →
-- String that creates a new string by placing its first argument between its
-- second and third arguments. joinStringsWith ", " "one" "and another" should
-- evaluate to "one, and another".

def joinStringsWith' sep before after :=
  String.append before $ String.append sep after

def joinStringsWith (sep before after : String) :=
  before ++ sep ++ after
  
#eval joinStringsWith ", " "one" "and another"                  

#check (joinStringsWith)                                                                 
#check (joinStringsWith ", ")                                                       
#check (joinStringsWith ", " "one")                                           
#check (joinStringsWith ", " "one" "and another")               

def volumeE  height width depth        := height * width * depth
def volume1 (height width depth : Nat) := height * width * depth
def volume2 (height : Nat) width depth := height * width * depth

#check  volume1                                                 
#check (volume1)                                                

#check  volume2                                                 
#check (volume2)                                                

/- -------------- -/
/- Defining Types -/
/- -------------- -/

-- https://lean-lang.org/functional_programming_in_lean/find/?domain=Verso.Genre.Manual.section&name=defining-types

def    Str1 := String
abbrev Str2 := String

#check Str1
#check Str2

def aStr : Str1    := "This is a string. "
def bStr : String  := "This is a string. "
def cStr : Str2    := "This is a string. "

#eval aStr ++ aStr                                             
#eval bStr ++ bStr                                             
#eval cStr ++ cStr                                             

/- --------------------- -/
/- Messages You May Meet -/
/- --------------------- -/

-- https://lean-lang.org/functional_programming_in_lean/find/?domain=Verso.Genre.Manual.section&name=abbrev-vs-def

def    NaturalNumber := Nat
-- abbrev NaturalNumber := Nat

#check NaturalNumber                                           

-- Lean allows number literals to be overloaded
def thirtyEight1 : Nat           :=  38
def thirtyEight2 : NaturalNumber :=  38                        
def thirtyEight3 : NaturalNumber := (38 : Nat)

abbrev N := Nat

def thirtyEight : N := 38
