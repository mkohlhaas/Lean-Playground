/- ============ -/
/- Alternatives -/
/- ============ -/

/- --------------------- -/
/- Recovery from Failure -/
/- --------------------- -/

/- --------------------- -/
/- The Alternative Class -/
/- --------------------- -/

/- ========= -/
/- Exercises -/
/- ========= -/

/- ------------------------------- -/
/- Improve Validation Friendliness -/
/- ------------------------------- -/

inductive TreeError where
  | field : Field → String → TreeError
  | path  : String → TreeError → TreeError
  | both  : TreeError → TreeError → TreeError

instance : Append TreeError where
  append := .both
