import Test.HUnit
import Test.Framework
import Test.Framework.Providers.HUnit
import Data.Monoid
import Control.Monad
import WLTrans
-- import NTRPTrans

ass = assertEqual "prova" 1 1
test1 = TestCase (assertEqual "prova" 1 1)
-- test2 = TestCase (WLTrans.main)
-- test2 = TestCase (do (x,y) <- partA 3
--                      assertEqual "for the first result of partA," 5 x
--                      b <- partB y
--                      assertBool ("(partB " ++ show y ++ ") failed") b)

-- tests = TestList [TestLabel "test1" WLTrans.main] --, TestLabel "test2" test2]

assertFailure :: String -> Assertion
assertFailure msg = ioError (userError ("HUnit:" ++ msg))

-- main :: IO ()
-- main = defaultMainWithOpts
--        [test "push" test1]
--        --,testCase "push-pop" pushPopTest]
--        mempty

main :: IO ()
main = defaultMainWithOpts
       [testCase "whitelisting forbidden" $ WLTrans.run whitelisting
       , testCase "whitelisting forbidden" $ WLTrans.run1 whitelisting
       -- , testCase "ntrp forbidden" $ NTRPTrans.run ntrp
       ]
       mempty