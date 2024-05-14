{-# OPTIONS_GHC -F -pgmF htfpp #-}
module AllTests ( allTests ) where

import {-@ HTF_TESTS @-} BasicTests
import {-@ HTF_TESTS @-} CduceTests
import Test.Framework

allTests :: IO ()
allTests = htfMain (htf_thisModulesTests : htf_importedTests)
