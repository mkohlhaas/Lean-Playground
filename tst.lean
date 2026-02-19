#eval 1 + 3 * 5

#eval String.append "Hello, " "Lean!"

#eval String.append "great " (String.append "oak " "tree")

#eval String.append "it is " (if 1 > 2 then "yes" else "no")

#eval 42 + 19

#eval String.append "A" (String.append "B" "C")

#eval String.append (String.append "A" "B") "C"

#eval if 3 == 3 then 5 else 7

#eval if 3 ==4 then "equal" else "not equal"

#eval (1 + 2 : Nat)

#eval 1 - 2

#eval (1 - 2 : Nat)

#eval (1 - 2 : Int)

#check (1 - 2 : Int)

#check (1 - 2)

/- #check String.append ["hello", " "] "world" -/

def hello := "Hello"

def lean : String := "Lean"

#eval String.append " " lean

#eval String.append hello (String.append " " lean)

def add1_1 n := n + 1

#eval add1_1 5

def add1_2 (n : Nat) : Nat := n + 1

#eval add1_2 5

/- def maximum1 n k : Nat := -/
/-   if n < k then -/
/-     k -/
/-   else n -/
  
def maximum2 (n : Nat) (k : Nat) : Nat :=
  if n < k then
    k
  else n 

#eval maximum2 2 5

def spaceBetween1 (before : String) (after : String) : String :=
  String.append before (String.append " " after)
  
/- def spaceBetween2 before after : String := -/
/-   String.append before (String.append " " after) -/

#check  spaceBetween1
#check (spaceBetween1)

/- Define the function joinStringsWith with type String → String → String → String that creates a new string by placing its first argument between its second and third arguments. joinStringsWith ", " "one" "and another" should evaluate to "one, and another". -/

def joinStringsWith sep before after := String.append before (String.append sep after)

#check joinStringsWith

#eval joinStringsWith ", " "one" "and another"

#check joinStringsWith ": "

def volume (height : Nat) width depth := height * width * depth

#check volume
#check (volume)
