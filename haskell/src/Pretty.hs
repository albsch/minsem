module Pretty (
    showPretty,
    module Prettyprinter
) where

import Prettyprinter

showPretty :: Pretty a => a -> String
showPretty = show . pretty
