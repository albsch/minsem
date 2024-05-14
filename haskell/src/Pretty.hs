module Pretty (
    showPretty,
    module Prettyprinter,
    maxPrec, withParens, PrettyPrec(..)
) where

import Prettyprinter

showPretty :: Pretty a => a -> String
showPretty = show . pretty

type Prec = Int

maxPrec :: Prec
maxPrec = 10

withParens :: Prec -> Prec -> Doc a -> Doc a
withParens outer inner d =
  if outer >= inner then parens d else d

class PrettyPrec a where
  -- precendence is the precendence of the surrounding context (as for showsPrec)
  prettyPrec :: Prec -> a -> Doc b
