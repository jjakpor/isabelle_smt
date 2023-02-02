# SMT in Isabelle/HOL

Formalization of [SMT-LIB Theories](https://smtlib.cs.uiowa.edu/theories.shtml) in Isabelle/HOL.

## File Structure

- `Core.thy`: Implementation of the [SMT-LIB core theory](https://smtlib.cs.uiowa.edu/theories-Core.shtml) (currently: shallow encoding)
- `Strings.thy`: Implementation of the quantifier-free [SMT-LIB string theory](https://smtlib.cs.uiowa.edu/theories-UnicodeStrings.shtml)
- `string/`:
  - `Words.thy`: Formalization of words (= strings)
  - `Regular.thy`: Formalization of regular languages including language derivatives
  - `RegEx.thy`: Formalization of regular expression including regex-derivatives
- `spec.json`: Contains the specification to convert SMT-LIB syntax to the internally used Isabelle syntax
