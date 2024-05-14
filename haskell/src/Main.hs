import AllTests
import CduceTestGen
import System.Environment

main :: IO ()
main = do
    args <- getArgs
    case args of
        [] -> allTests
        ["genTests", path, emptyCount, nonEmptyCount] ->
            genTests path (read emptyCount) (read nonEmptyCount)
        _ -> usage
    where
        usage = do
            putStrLn "USAGE: stack run [genTests path emptyCount nonEmptyCount]"
            putStrLn ""
            putStrLn "Runs the tests if invoked without arguments"
            putStrLn "genTests generates random test cases and stores them in path"

