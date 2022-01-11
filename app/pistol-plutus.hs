
import           Prelude

import           Cardano.Api

import           System.Directory
import           System.FilePath.Posix ((</>))

import           Cardano.Marketplace.Marketplace (tradeScript)

main :: IO ()
main = do
  let dir = "generated-plutus-scripts"
  createDirectory dir

  _ <- writeFileTextEnvelope (dir </> "plutus-marketplace.plutus") Nothing tradeScript
  return ()
