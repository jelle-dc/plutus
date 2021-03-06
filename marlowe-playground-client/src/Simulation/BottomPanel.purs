module Simulation.BottomPanel where

import Control.Alternative (map)
import Data.Array (concatMap, drop, head, length, reverse)
import Data.Array as Array
import Data.BigInteger (BigInteger)
import Data.Either (Either(..), either)
import Data.Eq (eq, (==))
import Data.Foldable (foldMap)
import Data.HeytingAlgebra (not, (||))
import Data.Lens (_Just, has, only, previewOn, to, (^.))
import Data.Lens.NonEmptyList (_Head)
import Data.List (List, null, toUnfoldable)
import Data.List as List
import Data.List.NonEmpty (toList)
import Data.Map as Map
import Data.Maybe (Maybe(..), isJust, isNothing)
import Data.Newtype (unwrap)
import Data.String (take)
import Data.String.Extra (unlines)
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested ((/\))
import Halogen.Classes (aHorizontal, accentBorderBottom, active, activeClass, closeDrawerArrowIcon, collapsed, first, flex, flexLeft, flexTen, footerPanelBg, minimizeIcon, rTable, rTable6cols, rTableCell, rTableDataRow, rTableEmptyRow, spanText, underline)
import Halogen.Classes as Classes
import Halogen.HTML (ClassName(..), HTML, a, a_, b_, br_, button, div, h2, h3, img, li, li_, ol, pre, section, span_, strong_, text, ul, ul_)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (alt, class_, classes, enabled, src)
import Marlowe.Semantics (Assets(..), ChoiceId(..), Input(..), Party, Payee(..), Payment(..), Slot(..), SlotInterval(..), Token(..), TransactionInput(..), TransactionWarning(..), ValueId(..), _accounts, _boundValues, _choices, showPrettyToken, timeouts)
import Marlowe.Symbolic.Types.Response as R
import Network.RemoteData (RemoteData(..), isLoading)
import Prelude (bind, const, mempty, pure, show, zero, ($), (&&), (<$>), (<<<), (<>))
import Servant.PureScript.Ajax (AjaxError(..), ErrorDescription(..))
import Simulation.Types (Action(..), AnalysisState(..), BottomPanelView(..), MarloweEvent(..), ReachabilityAnalysisData(..), State, _SimulationNotStarted, _SimulationRunning, _analysisState, _bottomPanelView, _contract, _editorErrors, _editorWarnings, _executionState, _initialSlot, _log, _marloweState, _showBottomPanel, _showErrorDetail, _slot, _state, _transactionError, _transactionWarnings, isContractValid)
import Text.Parsing.StringParser.Basic (lines)

bottomPanel :: forall p. State -> HTML p Action
bottomPanel state =
  div
    ( [ classes
          ( if showingBottomPanel then
              [ ClassName "simulation-bottom-panel" ]
            else
              [ ClassName "simulation-bottom-panel", collapsed ]
          )
      ]
    )
    [ div [ classes [ flex, ClassName "flip-x", ClassName "full-height" ] ]
        [ div [ class_ flexTen ]
            [ div [ classes [ footerPanelBg, active ] ]
                [ section [ classes [ ClassName "panel-header", aHorizontal ] ]
                    [ div [ classes [ ClassName "panel-sub-header-main", aHorizontal, accentBorderBottom ] ]
                        [ ul [ class_ (ClassName "start-item") ]
                            [ li [ class_ (ClassName "minimize-icon-container") ]
                                [ a [ onClick $ const $ Just $ ShowBottomPanel (state ^. _showBottomPanel <<< to not) ]
                                    [ img [ classes (minimizeIcon $ state ^. _showBottomPanel), src closeDrawerArrowIcon, alt "close drawer icon" ] ]
                                ]
                            ]
                        , ul [ classes [ ClassName "demo-list", aHorizontal ] ]
                            [ li
                                [ classes ((if hasRuntimeWarnings || hasRuntimeError then [ ClassName "error-tab" ] else []) <> isActive CurrentStateView)
                                , onClick $ const $ Just $ ChangeSimulationView CurrentStateView
                                ]
                                [ a_ [ text "Current State" ] ]
                            , li
                                [ classes ([] <> isActive StaticAnalysisView)
                                , onClick $ const $ Just $ ChangeSimulationView StaticAnalysisView
                                ]
                                [ a_ [ text "Static Analysis" ] ]
                            , li
                                [ classes ([] <> isActive MarloweWarningsView)
                                , onClick $ const $ Just $ ChangeSimulationView MarloweWarningsView
                                ]
                                [ a_ [ text $ "Warnings" <> if Array.null warnings then "" else " (" <> show (length warnings) <> ")" ] ]
                            , li
                                [ classes ([] <> isActive MarloweErrorsView)
                                , onClick $ const $ Just $ ChangeSimulationView MarloweErrorsView
                                ]
                                [ a_ [ text $ "Errors" <> if Array.null errors then "" else " (" <> show (length errors) <> ")" ] ]
                            , li
                                [ classes ([] <> isActive MarloweLogView)
                                , onClick $ const $ Just $ ChangeSimulationView MarloweLogView
                                ]
                                [ a_ [ text $ "Logs" ] ]
                            ]
                        ]
                    ]
                , panelContents state (state ^. _bottomPanelView)
                ]
            ]
        ]
    ]
  where
  isActive view = state ^. _bottomPanelView <<< (activeClass (eq view))

  warnings = state ^. (_marloweState <<< _Head <<< _editorWarnings)

  errors = state ^. (_marloweState <<< _Head <<< _editorErrors)

  hasRuntimeWarnings = has (_marloweState <<< _Head <<< _executionState <<< _SimulationRunning <<< _transactionWarnings <<< to Array.null <<< only false) state

  hasRuntimeError = has (_marloweState <<< _Head <<< _executionState <<< _SimulationRunning <<< _transactionError <<< to isJust <<< only true) state

  showingBottomPanel = state ^. _showBottomPanel

isStaticLoading :: AnalysisState -> Boolean
isStaticLoading (WarningAnalysis remoteData) = isLoading remoteData

isStaticLoading _ = false

isReachabilityLoading :: AnalysisState -> Boolean
isReachabilityLoading (ReachabilityAnalysis (InProgress _)) = true

isReachabilityLoading _ = false

panelContents :: forall p. State -> BottomPanelView -> HTML p Action
panelContents state CurrentStateView =
  div [ class_ Classes.panelContents ]
    [ div [ classes [ rTable, rTable6cols, ClassName "panel-table" ] ]
        ( warningsRow <> errorRow
            <> eitherRow "Current Slot" (slotText)
            <> dataRow "Expiration Slot" (state ^. (_marloweState <<< _Head <<< _contract <<< to contractMaxTime))
            <> tableRow
                { title: "Accounts"
                , emptyMessage: "No accounts have been used"
                , columns: ("Participant" /\ "Currency Symbol" /\ "Token Name" /\ "Money" /\ mempty)
                , rowData: accountsData
                }
            <> tableRow
                { title: "Choices"
                , emptyMessage: "No Choices have been made"
                , columns: ("Choice ID" /\ "Participant" /\ "Chosen Value" /\ mempty /\ mempty)
                , rowData: choicesData
                }
            <> tableRow
                { title: "Let Bindings"
                , emptyMessage: "No values have been bound"
                , columns: ("Identifier" /\ "Value" /\ mempty /\ mempty /\ mempty)
                , rowData: bindingsData
                }
        )
    ]
  where
  contractMaxTime Nothing = "Closed"

  contractMaxTime (Just contract) =
    let
      t = (_.maxTime <<< unwrap <<< timeouts) contract
    in
      if t == zero then "Closed" else show t

  warnings = state ^. (_marloweState <<< _Head <<< _executionState <<< _SimulationRunning <<< _transactionWarnings)

  warningsRow =
    if Array.null warnings then
      []
    else
      (headerRow "Warnings" ("type" /\ "details" /\ mempty /\ mempty /\ mempty)) <> foldMap displayWarning' warnings

  error = previewOn state (_marloweState <<< _Head <<< _executionState <<< _SimulationRunning <<< _transactionError <<< _Just)

  errorRow =
    if isNothing error then
      []
    else
      (headerRow "Errors" ("details" /\ mempty /\ mempty /\ mempty /\ mempty)) <> displayError error

  slotText = case previewOn state (_marloweState <<< _Head <<< _executionState <<< _SimulationNotStarted <<< _initialSlot) of
    Just initialSlot -> Right $ show initialSlot
    Nothing -> case previewOn state (_marloweState <<< _Head <<< _executionState <<< _SimulationRunning <<< _slot) of
      Just slot -> Right $ show slot
      Nothing -> Left "Slot number not defined"

  displayError Nothing = []

  displayError (Just err) =
    [ div [ classes [ rTableCell, first ] ] []
    , div [ classes [ rTableCell, ClassName "Rtable-single-column-row" ] ] [ text $ show err ]
    ]

  accountsData =
    let
      (accounts :: Array (Tuple (Tuple Party Token) BigInteger)) = state ^. (_marloweState <<< _Head <<< _executionState <<< _SimulationRunning <<< _state <<< _accounts <<< to Map.toUnfoldable)

      asTuple (Tuple (Tuple accountOwner (Token currSym tokName)) value) = show accountOwner /\ show currSym /\ show tokName /\ show value /\ mempty
    in
      map asTuple accounts

  choicesData =
    let
      (choices :: Array (Tuple ChoiceId BigInteger)) = state ^. (_marloweState <<< _Head <<< _executionState <<< _SimulationRunning <<< _state <<< _choices <<< to Map.toUnfoldable)

      asTuple (Tuple (ChoiceId choiceName choiceOwner) value) = show choiceName /\ show choiceOwner /\ show value /\ mempty /\ mempty
    in
      map asTuple choices

  bindingsData =
    let
      (bindings :: Array (Tuple ValueId BigInteger)) = state ^. (_marloweState <<< _Head <<< _executionState <<< _SimulationRunning <<< _state <<< _boundValues <<< to Map.toUnfoldable)

      asTuple (Tuple (ValueId valueId) value) = show valueId /\ show value /\ mempty /\ mempty /\ mempty
    in
      map asTuple bindings

  tableRow { title, emptyMessage, rowData: [] } = emptyRow title emptyMessage

  tableRow { title, columns, rowData } = headerRow title columns <> foldMap (\dataTuple -> row dataTuple) rowData

  headerRow title (a /\ b /\ c /\ d /\ e) =
    [ div [ classes [ rTableCell, first, Classes.header ] ] [ text title ] ]
      <> map (\x -> div [ classes [ rTableCell, rTableCell, Classes.header ] ] [ text x ]) [ a, b, c, d, e ]

  row (a /\ b /\ c /\ d /\ e) =
    [ div [ classes [ rTableCell, first ] ] [] ]
      <> map (\x -> div [ class_ rTableCell ] [ text x ]) [ a, b, c, d, e ]

  emptyRow title message =
    [ div [ classes [ rTableCell, first, Classes.header ] ]
        [ text title ]
    , div [ classes [ rTableCell, rTableEmptyRow, Classes.header ] ] [ text message ]
    ]

  dataRow title message =
    [ div [ classes [ rTableCell, first, Classes.header ] ]
        [ text title ]
    , div [ classes [ rTableCell, rTableDataRow ] ] [ text message ]
    ]

  eitherRow title = either (emptyRow title) (dataRow title)

  displayWarning' (TransactionNonPositiveDeposit party owner tok amount) =
    [ div [ classes [ rTableCell, first ] ] []
    , div [ class_ (ClassName "RTable-2-cells") ] [ text "TransactionNonPositiveDeposit" ]
    , div [ class_ (ClassName "RTable-4-cells") ]
        [ text $ "Party " <> show party <> " is asked to deposit " <> show amount
            <> " units of "
            <> showPrettyToken tok
            <> " into account of "
            <> show owner
            <> "."
        ]
    ]

  displayWarning' (TransactionNonPositivePay owner payee tok amount) =
    [ div [ classes [ rTableCell, first ] ] []
    , div [ class_ (ClassName "RTable-2-cells") ] [ text "TransactionNonPositivePay" ]
    , div [ class_ (ClassName "RTable-4-cells") ]
        [ text $ "The contract is supposed to make a payment of "
            <> show amount
            <> " units of "
            <> showPrettyToken tok
            <> " from account of "
            <> show owner
            <> " to "
            <> ( case payee of
                  (Account owner2) -> "account of " <> show owner2
                  (Party dest) -> "party " <> show dest
              )
            <> "."
        ]
    ]

  displayWarning' (TransactionPartialPay owner payee tok amount expected) =
    [ div [ classes [ rTableCell, first ] ] []
    , div [ class_ (ClassName "RTable-2-cells") ] [ text "TransactionPartialPay" ]
    , div [ class_ (ClassName "RTable-4-cells") ]
        [ text $ "The contract is supposed to make a payment of "
            <> show expected
            <> " units of "
            <> showPrettyToken tok
            <> " from account of "
            <> show owner
            <> " to "
            <> ( case payee of
                  (Account owner2) -> ("account of " <> show owner2)
                  (Party dest) -> ("party " <> show dest)
              )
            <> " but there is only "
            <> show amount
            <> "."
        ]
    ]

  displayWarning' (TransactionShadowing valId oldVal newVal) =
    [ div [ classes [ rTableCell, first ] ] []
    , div [ class_ (ClassName "RTable-2-cells") ] [ text "TransactionShadowing" ]
    , div [ class_ (ClassName "RTable-4-cells") ]
        [ text $ "The contract defined the value with id "
            <> show valId
            <> " before, it was assigned the value "
            <> show oldVal
            <> " and now it is being assigned the value "
            <> show newVal
            <> "."
        ]
    ]

  displayWarning' TransactionAssertionFailed =
    [ div [ classes [ rTableCell, first ] ] []
    , div [ class_ (ClassName "RTable-2-cells") ] [ text "TransactionAssertionFailed" ]
    , div [ class_ (ClassName "RTable-4-cells") ]
        [ text $ "An assertion in the contract did not hold." ]
    ]

panelContents state StaticAnalysisView =
  section
    [ classes [ ClassName "panel-sub-header", aHorizontal, Classes.panelContents ]
    ]
    [ analysisResultPane state
    , button [ onClick $ const $ Just $ AnalyseContract, enabled enabled', classes (if enabled' then [ ClassName "analyse-btn" ] else [ ClassName "analyse-btn", ClassName "disabled" ]) ]
        [ text (if loading then "Analysing..." else "Analyse for warnings") ]
    , button [ onClick $ const $ Just $ AnalyseReachabilityContract, enabled enabled', classes (if enabled' then [ ClassName "analyse-btn" ] else [ ClassName "analyse-btn", ClassName "disabled" ]) ]
        [ text (if loadingReachability then "Analysing..." else "Analyse reachability") ]
    ]
  where
  loading = state ^. _analysisState <<< to isStaticLoading

  loadingReachability = state ^. _analysisState <<< to isReachabilityLoading

  enabled' = not loading && not loadingReachability && isContractValid state

panelContents state MarloweWarningsView =
  section
    [ classes [ ClassName "panel-sub-header", aHorizontal, Classes.panelContents, flexLeft ]
    ]
    content
  where
  warnings = state ^. (_marloweState <<< _Head <<< _editorWarnings)

  content =
    if Array.null warnings then
      [ pre [ class_ (ClassName "error-content") ] [ text "No warnings" ] ]
    else
      [ div [ classes [ ClassName "error-headers", ClassName "error-row" ] ]
          [ div [] [ text "Description" ]
          , div [] [ text "Line Number" ]
          ]
      , ul_ (map renderWarning warnings)
      ]

  renderWarning warning =
    li [ classes [ ClassName "error-row" ] ]
      [ text warning.message
      , a
          [ onClick $ const $ Just $ MoveToPosition warning.startLineNumber warning.startColumn
          , class_ underline
          ]
          [ text $ show warning.startLineNumber ]
      ]

panelContents state MarloweErrorsView =
  section
    [ classes [ ClassName "panel-sub-header", aHorizontal, Classes.panelContents, flexLeft ]
    ]
    content
  where
  errors = state ^. (_marloweState <<< _Head <<< _editorErrors <<< to (map formatError))

  content =
    if Array.null errors then
      [ pre [ class_ (ClassName "error-content") ] [ text "No errors" ] ]
    else
      [ div [ classes [ ClassName "error-headers", ClassName "error-row" ] ]
          [ div [] [ text "Description" ]
          , div [] [ text "Line Number" ]
          ]
      , ul_ (map renderError errors)
      ]

  renderError error =
    li [ classes [ ClassName "error-row", ClassName "flex-wrap" ] ]
      ( [ a [ onClick $ const $ Just $ ShowErrorDetail (state ^. (_showErrorDetail <<< to not)) ]
            [ text $ (if state ^. _showErrorDetail then "- " else "+ ") <> error.firstLine ]
        , a
            [ onClick $ const $ Just $ MoveToPosition error.startLineNumber error.startColumn
            , class_ underline
            ]
            [ text $ show error.startLineNumber ]
        ]
          <> if (state ^. _showErrorDetail) then
              [ pre [ class_ (ClassName "error-content") ] [ text error.restLines ] ]
            else
              []
      )

  formatError { message, startColumn, startLineNumber } =
    let
      lines' = lines message

      firstLine /\ restLines =
        if (take 12 <$> head lines') == Just "Syntax error" then
          "Syntax error" /\ (unlines $ drop 2 lines')
        else
          "Error" /\ unlines lines'
    in
      { message, startColumn, startLineNumber, firstLine, restLines }

panelContents state MarloweLogView =
  section
    [ classes [ ClassName "panel-sub-header", aHorizontal, Classes.panelContents, flexLeft ]
    ]
    content
  where
  inputLines = state ^. (_marloweState <<< _Head <<< _executionState <<< _SimulationRunning <<< _log <<< to (concatMap logToLines))

  content =
    [ div [ classes [ ClassName "error-headers", ClassName "error-row" ] ]
        [ div [] [ text "Action" ]
        , div [] [ text "Slot" ]
        ]
    , ul [] (reverse inputLines)
    ]

analysisResultPane :: forall p. State -> HTML p Action
analysisResultPane state =
  let
    result = state ^. _analysisState

    explanation = div [ classes [ ClassName "padded-explanation" ] ]
  in
    case result of
      NoneAsked ->
        explanation
          [ text ""
          ]
      WarningAnalysis staticSubResult -> case staticSubResult of
        NotAsked ->
          explanation
            [ text ""
            ]
        Success (R.Valid) ->
          explanation
            [ h3 [ classes [ ClassName "analysis-result-title" ] ] [ text "Warning Analysis Result: Pass" ]
            , text "Static analysis could not find any execution that results in any warning."
            ]
        Success (R.CounterExample { initialSlot, transactionList, transactionWarning }) ->
          explanation
            [ h3 [ classes [ ClassName "analysis-result-title" ] ] [ text "Warning Analysis Result: Warnings Found" ]
            , text "Static analysis found the following counterexample:"
            , ul [ classes [ ClassName "indented-enum-initial" ] ]
                [ li_
                    [ spanText "Warnings issued: "
                    , displayWarningList transactionWarning
                    ]
                , li_
                    [ spanText "Initial slot: "
                    , b_ [ spanText (show initialSlot) ]
                    ]
                , li_
                    [ spanText "Offending transaction list: "
                    , displayTransactionList transactionList
                    ]
                ]
            ]
        Success (R.Error str) ->
          explanation
            [ h3 [ classes [ ClassName "analysis-result-title" ] ] [ text "Error during warning analysis" ]
            , text "Analysis failed for the following reason:"
            , ul [ classes [ ClassName "indented-enum-initial" ] ]
                [ li_
                    [ b_ [ spanText str ]
                    ]
                ]
            ]
        Failure (AjaxError { description }) ->
          let
            err = case description of
              DecodingError e -> "Decoding error: " <> e
              ConnectionError e -> "Connection error: " <> e
              ResponseFormatError e -> "Response Format error: " <> e
          in
            explanation
              [ h3 [ classes [ ClassName "analysis-result-title" ] ] [ text "Error during warning analysis" ]
              , text "Analysis failed for the following reason:"
              , ul [ classes [ ClassName "indented-enum-initial" ] ]
                  [ li_
                      [ b_ [ spanText err ]
                      ]
                  ]
              ]
        Loading -> text ""
      ReachabilityAnalysis reachabilitySubResult -> case reachabilitySubResult of
        NotStarted ->
          explanation
            [ text ""
            ]
        InProgress
          { numSubproblems: totalSteps
        , numSolvedSubproblems: doneSteps
        , unreachableSubcontracts: foundUnreachableSubcontracts
        } ->
          explanation
            ( [ text ("Reachability analysis in progress, " <> show doneSteps <> " subcontracts out of " <> show totalSteps <> " analysed...") ]
                <> if null foundUnreachableSubcontracts then
                    [ br_, text "No unreachable subcontracts found so far." ]
                  else
                    ( [ br_, text "Found the following unreachable subcontracts so far:" ]
                        <> [ ul [ classes [ ClassName "indented-enum-initial" ] ] do
                              contractPath <- toUnfoldable foundUnreachableSubcontracts
                              pure (li_ [ text (show contractPath) ])
                          ]
                    )
            )
        ReachabilityFailure err ->
          explanation
            [ h3 [ classes [ ClassName "analysis-result-title" ] ] [ text "Error during reachability analysis" ]
            , text "Reachability analysis failed for the following reason:"
            , ul [ classes [ ClassName "indented-enum-initial" ] ]
                [ li_
                    [ b_ [ spanText err ]
                    ]
                ]
            ]
        UnreachableSubcontract { unreachableSubcontracts } ->
          explanation
            ( [ h3 [ classes [ ClassName "analysis-result-title" ] ] [ text "Reachability Analysis Result: Unreachable Subcontract Found" ]
              , text "Static analysis found the following subcontracts that are unreachable:"
              ]
                <> [ ul [ classes [ ClassName "indented-enum-initial" ] ] do
                      contractPath <- toUnfoldable (toList unreachableSubcontracts)
                      pure (li_ [ text (show contractPath) ])
                  ]
            )
        AllReachable ->
          explanation
            [ h3 [ classes [ ClassName "analysis-result-title" ] ] [ text "Reachability Analysis Result: Pass" ]
            , text "Reachability analysis could not find any subcontract that is not reachable."
            ]

displayTransactionList :: forall p. Array TransactionInput -> HTML p Action
displayTransactionList transactionList =
  ol [ classes [ ClassName "indented-enum" ] ]
    ( do
        ( TransactionInput
            { interval: SlotInterval (Slot from) (Slot to)
          , inputs: inputList
          }
        ) <-
          transactionList
        pure
          ( li_
              [ span_
                  [ b_ [ text "Transaction" ]
                  , text " with slot interval "
                  , b_ [ text $ (show from <> " to " <> show to) ]
                  , if List.null inputList then
                      text " and no inputs (empty transaction)."
                    else
                      text " and inputs:"
                  ]
              , if List.null inputList then
                  text ""
                else
                  displayInputList inputList
              ]
          )
    )

displayInputList :: forall p. List Input -> HTML p Action
displayInputList inputList =
  ol [ classes [ ClassName "indented-loweralpha-enum" ] ]
    ( do
        input <- (toUnfoldable inputList)
        pure (li_ (displayInput input))
    )

displayInput :: forall p i. Input -> Array (HTML p i)
displayInput (IDeposit owner party tok money) =
  [ b_ [ text "IDeposit" ]
  , text " - Party "
  , b_ [ text $ show party ]
  , text " deposits "
  , b_ [ text $ show money ]
  , text " units of "
  , b_ [ text $ showPrettyToken tok ]
  , text " into account of "
  , b_ [ text (show owner) ]
  , text "."
  ]

displayInput (IChoice (ChoiceId choiceId party) chosenNum) =
  [ b_ [ text "IChoice" ]
  , text " - Party "
  , b_ [ text $ show party ]
  , text " chooses number "
  , b_ [ text $ show chosenNum ]
  , text " for choice "
  , b_ [ text $ show choiceId ]
  , text "."
  ]

displayInput (INotify) =
  [ b_ [ text "INotify" ]
  , text " - The contract is notified that an observation became "
  , b_ [ text "True" ]
  ]

displayWarningList :: forall p. Array TransactionWarning -> HTML p Action
displayWarningList transactionWarnings =
  ol [ classes [ ClassName "indented-enum" ] ]
    ( do
        warning <- transactionWarnings
        pure (li_ (displayWarning warning))
    )

displayWarnings :: forall p. Array TransactionWarning -> HTML p Action
displayWarnings [] = text mempty

displayWarnings warnings =
  div
    [ classes
        [ ClassName "invalid-transaction"
        , ClassName "input-composer"
        ]
    ]
    [ h2 [] [ text "Warnings" ]
    , ol
        []
        $ foldMap (\warning -> [ li_ (displayWarning warning) ]) warnings
    ]

displayWarning :: forall p. TransactionWarning -> Array (HTML p Action)
displayWarning (TransactionNonPositiveDeposit party owner tok amount) =
  [ b_ [ text "TransactionNonPositiveDeposit" ]
  , text " - Party "
  , b_ [ text $ show party ]
  , text " is asked to deposit "
  , b_ [ text $ show amount ]
  , text " units of "
  , b_ [ text $ showPrettyToken tok ]
  , text " into account of "
  , b_ [ text (show owner) ]
  , text "."
  ]

displayWarning (TransactionNonPositivePay owner payee tok amount) =
  [ b_ [ text "TransactionNonPositivePay" ]
  , text " - The contract is supposed to make a payment of "
  , b_ [ text $ show amount ]
  , text " units of "
  , b_ [ text $ showPrettyToken tok ]
  , text " from account of "
  , b_ [ text (show owner) ]
  , text " to "
  , b_
      [ text case payee of
          (Account owner2) -> ("account of " <> (show owner2))
          (Party dest) -> ("party " <> (show dest))
      ]
  , text "."
  ]

displayWarning (TransactionPartialPay owner payee tok amount expected) =
  [ b_ [ text "TransactionPartialPay" ]
  , text " - The contract is supposed to make a payment of "
  , b_ [ text $ show expected ]
  , text " units of "
  , b_ [ text $ showPrettyToken tok ]
  , text " from account of "
  , b_ [ text (show owner) ]
  , text " to "
  , b_
      [ text case payee of
          (Account owner2) -> ("account of " <> (show owner2))
          (Party dest) -> ("party " <> (show dest))
      ]
  , text " but there is only "
  , b_ [ text $ show amount ]
  , text "."
  ]

displayWarning (TransactionShadowing valId oldVal newVal) =
  [ b_ [ text "TransactionShadowing" ]
  , text " - The contract defined the value with id "
  , b_ [ text (show valId) ]
  , text " before, it was assigned the value "
  , b_ [ text (show oldVal) ]
  , text " and now it is being assigned the value "
  , b_ [ text (show newVal) ]
  , text "."
  ]

displayWarning TransactionAssertionFailed =
  [ b_ [ text "TransactionAssertionFailed" ]
  , text " - An assertion in the contract did not hold."
  ]

logToLines :: forall p a. MarloweEvent -> Array (HTML p a)
logToLines (InputEvent (TransactionInput { interval, inputs })) = Array.fromFoldable $ map (inputToLine interval) inputs

logToLines (OutputEvent interval payment) = paymentToLines interval payment

inputToLine :: forall p a. SlotInterval -> Input -> HTML p a
inputToLine (SlotInterval start end) (IDeposit accountOwner party token money) =
  li [ classes [ ClassName "error-row" ] ]
    [ span_
        [ text "Deposit "
        , strong_ [ text (show money) ]
        , text " units of "
        , strong_ [ text (showPrettyToken token) ]
        , text " into account of "
        , strong_ [ text (show accountOwner) ]
        , text " as "
        , strong_ [ text (show party) ]
        ]
    , span_ [ text $ (show start) <> " - " <> (show end) ]
    ]

inputToLine (SlotInterval start end) (IChoice (ChoiceId choiceName choiceOwner) chosenNum) =
  li [ classes [ ClassName "error-row" ] ]
    [ span_
        [ text "Participant "
        , strong_ [ text (show choiceOwner) ]
        , text " chooses the value "
        , strong_ [ text (show chosenNum) ]
        , text " for choice with id "
        , strong_ [ text (show choiceName) ]
        ]
    , span_ [ text $ (show start) <> " - " <> (show end) ]
    ]

inputToLine (SlotInterval start end) INotify =
  li [ classes [ ClassName "error-row" ] ]
    [ text "Notify"
    , span_ [ text $ (show start) <> " - " <> (show end) ]
    ]

paymentToLines :: forall p a. SlotInterval -> Payment -> Array (HTML p a)
paymentToLines slotInterval (Payment party money) = unfoldAssets money (paymentToLine slotInterval party)

paymentToLine :: forall p a. SlotInterval -> Party -> Token -> BigInteger -> HTML p a
paymentToLine (SlotInterval start end) party token money =
  li [ classes [ ClassName "error-row" ] ]
    [ span_
        [ text "The contract pays "
        , strong_ [ text (show money) ]
        , text " units of "
        , strong_ [ text (showPrettyToken token) ]
        , text " to participant "
        , strong_ [ text (show party) ]
        ]
    , span_ [ text $ (show start) <> " - " <> (show end) ]
    ]

unfoldAssets :: forall a. Assets -> (Token -> BigInteger -> a) -> Array a
unfoldAssets (Assets mon) f =
  concatMap
    ( \(Tuple currencySymbol tokenMap) ->
        ( map
            ( \(Tuple tokenName value) ->
                f (Token currencySymbol tokenName) value
            )
            (Map.toUnfoldable tokenMap)
        )
    )
    (Map.toUnfoldable mon)
