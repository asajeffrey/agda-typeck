module Luau.Type.ToString where

open import FFI.Data.String using (String; _++_)
open import Luau.Type using (Type; Test; scalar; _⇒_; never; any; check; NIL; NUMBER; BOOLEAN; STRING; error; function; _∪_; _∩_; normalizeOptional)

{-# TERMINATING #-}
testToString : Test → String
testToStringᵁ : Test → String
testToStringᴵ : Test → String

testToString (scalar NIL) = "nil"
testToString (scalar NUMBER) = "number"
testToString (scalar BOOLEAN) = "boolean"
testToString (scalar STRING) = "string"
testToString function = "function"
testToString never = "never"
testToString (S ∪ T) = "(" ++ testToStringᵁ (S ∪ T) ++ ")"
testToString (S ∩ T) = "(" ++ testToStringᴵ (S ∩ T) ++ ")"

testToStringᵁ (S ∪ T) = (testToStringᵁ S) ++ " | " ++ (testToStringᵁ T)
testToStringᵁ T = testToStringᵁ T

testToStringᴵ (S ∩ T) = (testToStringᴵ S) ++ " | " ++ (testToStringᴵ T)
testToStringᴵ T = testToString T

{-# TERMINATING #-}
typeToString : Type → String
typeToStringᵁ : Type → String
typeToStringᴵ : Type → String

typeToString (S ⇒ T) = "(" ++ (typeToString S) ++ ") -> " ++ (typeToString T)
typeToString (check S) = "(" ++ (testToString S) ++ ") -> error"
typeToString never = "never"
typeToString any = "any"
typeToString (scalar NIL) = "nil"
typeToString (scalar NUMBER) = "number"
typeToString (scalar BOOLEAN) = "boolean"
typeToString (scalar STRING) = "string"
typeToString error = "error"
typeToString (S ∪ T) with normalizeOptional(S ∪ T)
typeToString (S ∪ T) | (((((never ⇒ any) ∪ (scalar NUMBER)) ∪ (scalar STRING)) ∪ (scalar BOOLEAN)) ∪ (scalar NIL)) = "unknown"
typeToString (S ∪ T) | ((S′ ⇒ T′) ∪ scalar NIL) = "(" ++ typeToString (S′ ⇒ T′) ++ ")?"
typeToString (S ∪ T) | (S′ ∪ scalar NIL) = typeToString S′ ++ "?"
typeToString (S ∪ T) | (S′ ∪ T′) = "(" ++ typeToStringᵁ (S ∪ T) ++ ")"
typeToString (S ∪ T) | T′ = typeToString T′
typeToString (S ∩ T) = "(" ++ typeToStringᴵ (S ∩ T) ++ ")"

typeToStringᵁ (S ∪ T) = (typeToStringᵁ S) ++ " | " ++ (typeToStringᵁ T)
typeToStringᵁ T = typeToString T

typeToStringᴵ (S ∩ T) = (typeToStringᴵ S) ++ " & " ++ (typeToStringᴵ T)
typeToStringᴵ T = typeToString T
