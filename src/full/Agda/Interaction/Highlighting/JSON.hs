{-# OPTIONS_GHC -Wunused-imports #-}

-- | Functions which give precise syntax highlighting info in JSON format.

module Agda.Interaction.Highlighting.JSON (jsonifyHighlightingInfo) where

import qualified Data.ByteString.Lazy.Char8 as BS

import Agda.Interaction.Highlighting.Common
import Agda.Interaction.Highlighting.Precise hiding (String)
import Agda.Interaction.Highlighting.Range (Range(..))
import Agda.Interaction.JSON
import Agda.Interaction.Response

import Agda.TypeChecking.Monad (HighlightingMethod(..), ModuleToSource, topLevelModuleFilePath)

import Agda.Utils.FileName     (AbsolutePath, filePath)
import Agda.Utils.IO.TempFile  (writeToTempFile)
import Agda.Utils.CallStack    (HasCallStack)

-- | Encode meta information into a JSON Value
showAspects
  :: ModuleToSource
     -- ^ Must contain a mapping for the definition site's module, if any.
  -> (Range, Aspects) -> Value
showAspects modFile (range, aspect) = object
  [ "range" .= [from range, to range]
  , "atoms" .= toAtoms aspect
  , "tokenBased" .= tokenBased aspect
  , "note" .= note aspect
  , "definitionSite" .= fmap defSite (definitionSite aspect)
  ]
  where
    defSite (DefinitionSite mdl position _ _) = object
      [ "filepath" .= filePath f
      , "position" .= position
      ]
      where
        f :: HasCallStack => AbsolutePath
        f = topLevelModuleFilePath modFile mdl  -- partial function, so use CallStack!

instance EncodeTCM TokenBased where
instance ToJSON TokenBased where
    toJSON TokenBased = String "TokenBased"
    toJSON NotOnlyTokenBased = String "NotOnlyTokenBased"

-- | Turns syntax highlighting information into a JSON value
jsonifyHighlightingInfo
  :: HighlightingInfo
  -> RemoveTokenBasedHighlighting
  -> HighlightingMethod
  -> ModuleToSource
     -- ^ Must contain a mapping for every definition site's module.
  -> IO Value
jsonifyHighlightingInfo info remove method modFile =
  case chooseHighlightingMethod info method of
    Direct   -> direct
    Indirect -> indirect
  where
    result :: Value
    result = object
      [ "remove" .= case remove of
          RemoveHighlighting -> True
          KeepHighlighting -> False
      , "payload" .= map (showAspects modFile) (toList info)
      ]

    direct :: IO Value
    direct = return $ object
      [ "kind"   .= String "HighlightingInfo"
      , "direct" .= True
      , "info"   .= result
      ]

    indirect :: IO Value
    indirect = do
      filepath <- writeToTempFile (BS.unpack (encode result))
      return $ object
        [ "kind"     .= String "HighlightingInfo"
        , "direct"   .= False
        , "filepath" .= filepath
        ]
