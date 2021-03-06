module Simulation where

import Control.Alternative (map, void, when, (<*>), (<|>))
import Control.Monad.Except (ExceptT, runExceptT, runExcept)
import Control.Monad.Reader (runReaderT)
import Data.Array (delete, filter, intercalate, snoc, sortWith)
import Data.Array as Array
import Data.BigInteger (BigInteger, fromString, fromInt)
import Data.Decimal (truncated, fromNumber)
import Data.Decimal as Decimal
import Data.Either (Either(..))
import Data.Enum (toEnum, upFromIncluding)
import Data.EuclideanRing ((*))
import Data.HeytingAlgebra (not, (&&))
import Data.Lens (assign, has, modifying, only, over, preview, to, use, view, (^.))
import Data.Lens.Extra (peruse)
import Data.Lens.Index (ix)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.NonEmptyList (_Head)
import Data.List.NonEmpty as NEL
import Data.List.Types (List(..), NonEmptyList)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (wrap)
import Data.NonEmptyList.Extra (tailIfNotEmpty)
import Data.RawJson (RawJson(..))
import Data.String (codePointFromChar)
import Data.String as String
import Data.Traversable (for_, traverse)
import Data.Tuple (Tuple(..), snd)
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Console (log)
import FileEvents (readFileFromDragEvent)
import FileEvents as FileEvents
import Foreign.Generic (ForeignError, decode)
import Foreign.JSON (parseJSON)
import Halogen (HalogenM, get, query)
import Halogen.Classes (aHorizontal, activeClasses, bold, closeDrawerIcon, codeEditor, expanded, fullHeight, infoIcon, noMargins, panelSubHeaderSide, plusBtn, pointer, scroll, sidebarComposer, smallBtn, spanText, textSecondaryColor, uppercase)
import Halogen.Classes as Classes
import Halogen.HTML (ClassName(..), ComponentHTML, HTML, a, article, aside, b_, br_, button, div, em_, h6, h6_, img, input, li, option, p, p_, section, select, slot, small, strong_, text, ul, ul_)
import Halogen.HTML.Events (onClick, onSelectedIndexChange, onValueChange)
import Halogen.HTML.Properties (InputType(..), alt, class_, classes, enabled, placeholder, src, type_, value)
import Halogen.HTML.Properties as HTML
import Halogen.Monaco (Message(..), Query(..)) as Monaco
import Halogen.Monaco (monacoComponent)
import Help (HelpContext(..), toHTML)
import LocalStorage as LocalStorage
import MainFrame.Types (ChildSlots, _marloweEditorSlot)
import Marlowe (SPParams_)
import Marlowe as Server
import Marlowe.Linter as Linter
import Marlowe.Monaco (updateAdditionalContext)
import Marlowe.Monaco as MM
import Marlowe.Parser (parseContract)
import Marlowe.Semantics (AccountId, Bound(..), ChoiceId(..), Input(..), Party(..), PubKey, Token, emptyState, inBounds, showPrettyToken)
import Marlowe.Symbolic.Types.Request as MSReq
import Monaco (IMarker, isError, isWarning)
import Monaco (getModel, getMonaco, setTheme, setValue) as Monaco
import Network.RemoteData (RemoteData(..))
import Network.RemoteData as RemoteData
import Prelude (class Show, Unit, Void, bind, bottom, const, discard, eq, flip, identity, mempty, pure, show, unit, zero, ($), (-), (/=), (<), (<$>), (<<<), (<>), (=<<), (==), (>=))
import Projects.Types (Lang(..))
import Reachability (areContractAndStateTheOnesAnalysed, getUnreachableContracts, startReachabilityAnalysis)
import Servant.PureScript.Ajax (AjaxError, errorToString)
import Servant.PureScript.Settings (SPSettings_)
import Simulation.BottomPanel (bottomPanel)
import Simulation.State (applyInput, getAsMuchStateAsPossible, hasHistory, inFuture, moveToSignificantSlot, moveToSlot, nextSignificantSlot, updateContractInState, updateMarloweState)
import Simulation.Types (Action(..), ActionInput(..), ActionInputId(..), AnalysisState(..), ExecutionState(..), Parties(..), State, WebData, _SimulationNotStarted, _SimulationRunning, _activeDemo, _analysisState, _bottomPanelView, _contract, _currentContract, _currentMarloweState, _editorErrors, _editorKeybindings, _editorWarnings, _executionState, _helpContext, _initialSlot, _marloweState, _moveToAction, _oldContract, _pendingInputs, _possibleActions, _selectedHole, _showBottomPanel, _showErrorDetail, _showRightPanel, _slot, _source, emptyExecutionStateWithSlot, emptyMarloweState, isContractValid, mapPartiesActionInput, otherActionsParty)
import StaticData (marloweBufferLocalStorageKey)
import StaticData as StaticData
import Text.Pretty (genericPretty, pretty)
import Web.DOM.Document as D
import Web.DOM.Element (setScrollTop)
import Web.DOM.Element as E
import Web.DOM.HTMLCollection as WC
import Web.HTML as Web
import Web.HTML.HTMLDocument (toDocument)
import Web.HTML.Window as W

handleAction ::
  forall m.
  MonadEffect m =>
  MonadAff m =>
  SPSettings_ SPParams_ -> Action -> HalogenM State Action ChildSlots Void m Unit
handleAction settings Init = do
  editorSetTheme
  setOraclePrice settings

handleAction settings (HandleEditorMessage (Monaco.TextChanged "")) = do
  assign _marloweState $ NEL.singleton emptyMarloweState
  assign _oldContract Nothing
  updateContractInState ""

handleAction settings (HandleEditorMessage (Monaco.TextChanged text)) = do
  assign _selectedHole Nothing
  liftEffect $ LocalStorage.setItem marloweBufferLocalStorageKey text
  updateContractInState text
  assign _activeDemo ""
  executionState <- use (_currentMarloweState <<< _executionState)
  analysisState <- use _analysisState
  currContract <- use (_currentMarloweState <<< _contract)
  currState <- getAsMuchStateAsPossible
  let
    reachabilityResultsValid = areContractAndStateTheOnesAnalysed analysisState currContract currState

    unreachableContracts = if reachabilityResultsValid then getUnreachableContracts analysisState else Nil

    state = case executionState of
      SimulationRunning runRecord -> runRecord.state
      SimulationNotStarted notRunRecord -> emptyState $ notRunRecord.initialSlot

    (Tuple markerData additionalContext) = Linter.markers unreachableContracts state text
  markers <- query _marloweEditorSlot unit (Monaco.SetModelMarkers markerData identity)
  void $ traverse editorSetMarkers markers
  objects <- query _marloweEditorSlot unit (Monaco.GetObjects identity)
  case objects of
    Just { codeActionProvider: Just caProvider, completionItemProvider: Just ciProvider } -> pure $ updateAdditionalContext caProvider ciProvider additionalContext
    _ -> pure unit

handleAction _ (HandleDragEvent event) = liftEffect $ FileEvents.preventDefault event

handleAction settings (HandleDropEvent event) = do
  liftEffect $ FileEvents.preventDefault event
  contents <- liftAff $ readFileFromDragEvent event
  void $ editorSetValue contents
  updateContractInState contents
  setOraclePrice settings

handleAction _ (MoveToPosition lineNumber column) = do
  void $ query _marloweEditorSlot unit (Monaco.SetPosition { column, lineNumber } unit)

handleAction _ (SelectEditorKeyBindings bindings) = do
  assign _editorKeybindings bindings
  void $ query _marloweEditorSlot unit (Monaco.SetKeyBindings bindings unit)

handleAction settings (LoadScript key) = do
  for_ (preview (ix key) StaticData.marloweContracts) \contents -> do
    let
      prettyContents = case parseContract contents of
        Right pcon -> show $ pretty pcon
        Left _ -> contents
    editorSetValue prettyContents
    liftEffect $ LocalStorage.setItem marloweBufferLocalStorageKey prettyContents
    updateContractInState prettyContents
    resetContract
    assign _activeDemo key
    setOraclePrice settings

handleAction settings (SetEditorText contents) = do
  editorSetValue contents
  updateContractInState contents

handleAction settings (SetInitialSlot initialSlot) = do
  assign (_currentMarloweState <<< _executionState <<< _SimulationNotStarted <<< _initialSlot) initialSlot
  setOraclePrice settings

handleAction settings StartSimulation = do
  maybeInitialSlot <- peruse (_currentMarloweState <<< _executionState <<< _SimulationNotStarted <<< _initialSlot)
  for_ maybeInitialSlot \initialSlot -> do
    saveInitialState
    assign (_currentMarloweState <<< _executionState) (emptyExecutionStateWithSlot initialSlot)
    moveToSignificantSlot initialSlot
    mCurrContract <- use _currentContract
    case mCurrContract of
      Just currContract -> do
        editorSetValue (show $ genericPretty currContract)
        setOraclePrice settings
      Nothing -> pure unit

handleAction settings (MoveSlot slot) = do
  inTheFuture <- inFuture <$> get <*> pure slot
  significantSlot <- use (_marloweState <<< _Head <<< to nextSignificantSlot)
  when inTheFuture do
    saveInitialState
    if slot >= (fromMaybe zero significantSlot) then
      moveToSignificantSlot slot
    else
      moveToSlot slot
    mCurrContract <- use _currentContract
    case mCurrContract of
      Just currContract -> do
        editorSetValue (show $ genericPretty currContract)
        setOraclePrice settings
      Nothing -> pure unit

handleAction settings (SetSlot slot) = do
  assign (_currentMarloweState <<< _executionState <<< _SimulationRunning <<< _possibleActions <<< _moveToAction) (Just $ MoveToSlot slot)
  setOraclePrice settings

handleAction settings (AddInput input bounds) = do
  when validInput do
    saveInitialState
    applyInput ((flip snoc) input)
    mCurrContract <- use _currentContract
    case mCurrContract of
      Just currContract -> do
        editorSetValue (show $ genericPretty currContract)
        setOraclePrice settings
      Nothing -> pure unit
  where
  validInput = case input of
    (IChoice _ chosenNum) -> inBounds chosenNum bounds
    _ -> true

handleAction settings (RemoveInput input) = do
  updateMarloweState (over (_executionState <<< _SimulationRunning <<< _pendingInputs) (delete input))
  currContract <- editorGetValue
  case currContract of
    Nothing -> pure unit
    Just contract -> do
      updateContractInState contract
      setOraclePrice settings

handleAction _ (SetChoice choiceId chosenNum) = updateMarloweState (over (_executionState <<< _SimulationRunning <<< _possibleActions) (mapPartiesActionInput (updateChoice choiceId)))
  where
  updateChoice :: ChoiceId -> ActionInput -> ActionInput
  updateChoice wantedChoiceId input@(ChoiceInput currentChoiceId bounds _)
    | wantedChoiceId == currentChoiceId = ChoiceInput choiceId bounds chosenNum

  updateChoice _ input = input

handleAction settings ResetSimulator = do
  oldContract <- use _oldContract
  currContract <- editorGetValue
  let
    newContract = fromMaybe mempty $ oldContract <|> currContract
  editorSetValue newContract
  resetContract
  setOraclePrice settings

handleAction settings ResetContract = do
  resetContract
  setOraclePrice settings

handleAction settings Undo = do
  modifying _marloweState tailIfNotEmpty
  mCurrContract <- use _currentContract
  case mCurrContract of
    Just currContract -> do
      editorSetValue (show $ genericPretty currContract)
      setOraclePrice settings
    Nothing -> pure unit

handleAction _ (SelectHole hole) = assign _selectedHole hole

handleAction _ (ChangeSimulationView view) = do
  assign _bottomPanelView view
  assign _showBottomPanel true
  editorResize

handleAction _ (ChangeHelpContext help) = do
  assign _helpContext help
  scrollHelpPanel

handleAction _ (ShowRightPanel val) = assign _showRightPanel val

handleAction _ (ShowBottomPanel val) = do
  assign _showBottomPanel val
  editorResize

handleAction _ (ShowErrorDetail val) = assign _showErrorDetail val

handleAction _ SetBlocklyCode = pure unit

handleAction _ EditHaskell = pure unit

handleAction _ EditJavascript = pure unit

handleAction _ EditActus = pure unit

handleAction settings AnalyseContract = do
  currContract <- use _currentContract
  currState <- getAsMuchStateAsPossible
  case currContract of
    Nothing -> pure unit
    Just contract -> do
      assign _analysisState (WarningAnalysis Loading)
      response <- checkContractForWarnings contract currState
      assign _analysisState (WarningAnalysis response)
  where
  checkContractForWarnings contract state = runAjax $ (flip runReaderT) settings (Server.postMarloweanalysis (MSReq.Request { onlyAssertions: false, contract, state }))

handleAction settings AnalyseReachabilityContract = do
  currContract <- use _currentContract
  currState <- getAsMuchStateAsPossible
  case currContract of
    Nothing -> pure unit
    Just contract -> do
      newReachabilityAnalysisState <- startReachabilityAnalysis settings contract currState
      assign _analysisState (ReachabilityAnalysis newReachabilityAnalysisState)

handleAction _ Save = pure unit

setOraclePrice ::
  forall m.
  MonadAff m =>
  SPSettings_ SPParams_ -> HalogenM State Action ChildSlots Void m Unit
setOraclePrice settings = do
  execState <- use (_currentMarloweState <<< _executionState)
  case execState of
    SimulationRunning esr -> do
      let
        (Parties actions) = esr.possibleActions
      case Map.lookup (Role "kraken") actions of
        Just acts -> do
          case Array.head (Map.toUnfoldable acts) of
            Just (Tuple (ChoiceInputId choiceId@(ChoiceId pair _)) _) -> do
              price <- getPrice settings "kraken" pair
              handleAction settings (SetChoice choiceId price)
            _ -> pure unit
        Nothing -> pure unit
    _ -> pure unit

type Resp
  = { result :: { price :: Number }, allowance :: { remaining :: Number, upgrade :: String, cost :: Number } }

getPrice :: forall m. MonadAff m => SPSettings_ SPParams_ -> String -> String -> HalogenM State Action ChildSlots Void m BigInteger
getPrice settings exchange pair = do
  result <- runAjax (runReaderT (Server.getApiOracleByExchangeByPair exchange pair) settings)
  calculatedPrice <-
    liftEffect case result of
      NotAsked -> pure "0"
      Loading -> pure "0"
      Failure e -> do
        log $ "Failure" <> errorToString e
        pure "0"
      Success (RawJson json) -> do
        let
          response :: Either (NonEmptyList ForeignError) Resp
          response =
            runExcept
              $ do
                  foreignJson <- parseJSON json
                  decode foreignJson
        case response of
          Right resp -> do
            let
              price = fromNumber resp.result.price
            let
              adjustedPrice = price * fromNumber 100000000.0
            log $ "Got price: " <> show resp.result.price <> ", remaining calls: " <> show resp.allowance.remaining
            pure $ Decimal.toString (truncated adjustedPrice)
          Left err -> do
            log $ "Left " <> show err
            pure "0"
  let
    price = fromMaybe zero (fromString calculatedPrice)
  pure price

getCurrentContract :: forall m. HalogenM State Action ChildSlots Void m String
getCurrentContract = do
  oldContract <- use _oldContract
  currContract <- editorGetValue
  pure $ fromMaybe mempty $ oldContract <|> currContract

runAjax ::
  forall m a.
  ExceptT AjaxError (HalogenM State Action ChildSlots Void m) a ->
  HalogenM State Action ChildSlots Void m (WebData a)
runAjax action = RemoteData.fromEither <$> runExceptT action

scrollHelpPanel :: forall m. MonadEffect m => HalogenM State Action ChildSlots Void m Unit
scrollHelpPanel =
  liftEffect do
    window <- Web.window
    document <- toDocument <$> W.document window
    mSidePanel <- WC.item 0 =<< D.getElementsByClassName "sidebar-composer" document
    mDocPanel <- WC.item 0 =<< D.getElementsByClassName "documentation-panel" document
    case mSidePanel, mDocPanel of
      Just sidePanel, Just docPanel -> do
        sidePanelHeight <- E.scrollHeight sidePanel
        docPanelHeight <- E.scrollHeight docPanel
        availableHeight <- E.clientHeight sidePanel
        let
          newScrollHeight =
            if sidePanelHeight < availableHeight then
              sidePanelHeight
            else
              sidePanelHeight - docPanelHeight - 120.0
        setScrollTop newScrollHeight sidePanel
      _, _ -> pure unit

editorSetTheme :: forall state action msg m. HalogenM state action ChildSlots msg m Unit
editorSetTheme = void $ query _marloweEditorSlot unit (Monaco.SetTheme MM.daylightTheme.name unit)

editorResize :: forall state action msg m. HalogenM state action ChildSlots msg m Unit
editorResize = void $ query _marloweEditorSlot unit (Monaco.Resize unit)

editorSetValue :: forall state action msg m. String -> HalogenM state action ChildSlots msg m Unit
editorSetValue contents = void $ query _marloweEditorSlot unit (Monaco.SetText contents unit)

editorGetValue :: forall state action msg m. HalogenM state action ChildSlots msg m (Maybe String)
editorGetValue = query _marloweEditorSlot unit (Monaco.GetText identity)

saveInitialState :: forall m. MonadEffect m => HalogenM State Action ChildSlots Void m Unit
saveInitialState = do
  oldContract <- editorGetValue
  modifying _oldContract
    ( \x -> case x of
        Nothing -> Just $ fromMaybe "" oldContract
        _ -> x
    )

resetContract :: forall m. HalogenM State Action ChildSlots Void m Unit
resetContract = do
  newContract <- editorGetValue
  assign _marloweState $ NEL.singleton emptyMarloweState
  assign _oldContract Nothing
  updateContractInState $ fromMaybe "" newContract

editorSetMarkers :: forall m. MonadEffect m => Array IMarker -> HalogenM State Action ChildSlots Void m Unit
editorSetMarkers markers = do
  let
    warnings = filter (\{ severity } -> isWarning severity) markers

    trimHoles =
      map
        ( \marker ->
            let
              trimmedMessage =
                if String.take 6 marker.source == "Hole: " then
                  String.takeWhile (\c -> c /= codePointFromChar '\n') marker.message
                else
                  marker.message
            in
              marker { message = trimmedMessage }
        )
        warnings
  let
    errors = filter (\{ severity } -> isError severity) markers
  assign (_marloweState <<< _Head <<< _editorWarnings) trimHoles
  assign (_marloweState <<< _Head <<< _editorErrors) errors
  pure unit

render ::
  forall m.
  MonadAff m =>
  State ->
  ComponentHTML Action ChildSlots m
render state =
  div [ classes [ fullHeight, scroll, ClassName "simulation-panel" ] ]
    [ section [ class_ (ClassName "code-panel") ]
        [ div [ classes (codeEditor $ state ^. _showBottomPanel) ]
            [ marloweEditor state ]
        , sidebar state
        ]
    , bottomPanel state
    ]
  where
  showRightPanel = state ^. _showRightPanel

  demoScriptLink key =
    li [ state ^. _activeDemo <<< activeClasses (eq key) ]
      [ a [ onClick $ const $ Just $ LoadScript key ] [ text key ] ]

otherActions :: forall p. State -> HTML p Action
otherActions state =
  div [ classes [ ClassName "group" ] ]
    ( [ editorOptions state
      , sendToBlocklyButton state
      ]
        <> ( if has (_source <<< only Haskell) state then
              [ haskellSourceButton state ]
            else
              []
          )
        <> ( if has (_source <<< only Javascript) state then
              [ javascriptSourceButton state ]
            else
              []
          )
        <> ( if has (_source <<< only Actus) state then
              [ actusSourceButton state ]
            else
              []
          )
    )

sendToBlocklyButton :: forall p. State -> HTML p Action
sendToBlocklyButton state =
  button
    [ onClick $ const $ Just $ SetBlocklyCode
    , enabled isBlocklyEnabled
    , classes [ Classes.disabled (not isBlocklyEnabled) ]
    ]
    [ text "View in Blockly Editor" ]
  where
  isBlocklyEnabled = view (_marloweState <<< _Head <<< _editorErrors <<< to Array.null) state

haskellSourceButton :: forall p. State -> HTML p Action
haskellSourceButton state =
  button
    [ onClick $ const $ Just $ EditHaskell
    ]
    [ text "Edit Haskell Source" ]

javascriptSourceButton :: forall p. State -> HTML p Action
javascriptSourceButton state =
  button
    [ onClick $ const $ Just $ EditJavascript
    ]
    [ text "Edit Javascript Source" ]

actusSourceButton :: forall p. State -> HTML p Action
actusSourceButton state =
  button
    [ onClick $ const $ Just $ EditActus
    ]
    [ text "Edit Actus Source" ]

editorOptions :: forall p. State -> HTML p Action
editorOptions state =
  div [ class_ (ClassName "editor-options") ]
    [ select
        [ HTML.id_ "editor-options"
        , class_ (ClassName "dropdown-header")
        , onSelectedIndexChange (\idx -> SelectEditorKeyBindings <$> toEnum idx)
        ]
        (map keybindingItem (upFromIncluding bottom))
    ]
  where
  keybindingItem item =
    if state ^. _editorKeybindings == item then
      option [ class_ (ClassName "selected-item"), HTML.value (show item) ] [ text $ show item ]
    else
      option [ HTML.value (show item) ] [ text $ show item ]

marloweEditor ::
  forall m.
  MonadAff m =>
  State ->
  ComponentHTML Action ChildSlots m
marloweEditor state = slot _marloweEditorSlot unit component unit (Just <<< HandleEditorMessage)
  where
  setup editor = do
    mContents <- liftEffect $ LocalStorage.getItem StaticData.marloweBufferLocalStorageKey
    let
      contents = fromMaybe "?contract" (mContents <|> Map.lookup "Example" StaticData.marloweContracts)
    model <- liftEffect $ Monaco.getModel editor
    liftEffect do
      Monaco.setValue model contents
      -- Since the Simulation Tab is viewed before the Haskell tab we need to set the correct editor theme when things have been loaded
      monaco <- Monaco.getMonaco
      Monaco.setTheme monaco MM.daylightTheme.name

  component = monacoComponent $ MM.settings setup

sidebar ::
  forall p.
  State ->
  HTML p Action
sidebar state =
  let
    showRightPanel = state ^. _showRightPanel
  in
    aside [ classes [ sidebarComposer, expanded showRightPanel ] ]
      [ div [ classes [ panelSubHeaderSide, expanded (state ^. _showRightPanel), ClassName "drawer-icon-container" ] ]
          [ a [ classes [ (ClassName "drawer-icon-click") ], onClick $ const $ Just $ ShowRightPanel (not showRightPanel) ]
              [ img [ src closeDrawerIcon, class_ (ClassName "drawer-icon") ] ]
          ]
      , div [ classes [ aHorizontal, ClassName "transaction-composer" ] ]
          [ h6 [ classes [ ClassName "input-composer-heading", noMargins ] ]
              [ small [ classes [ textSecondaryColor, bold, uppercase ] ] [ text "Available Actions" ] ]
          , a [ onClick $ const $ Just $ ChangeHelpContext AvailableActionsHelp ] [ img [ src infoIcon, alt "info book icon" ] ]
          ]
      , transactionComposer state
      , article [ class_ (ClassName "documentation-panel") ]
          (toHTML (state ^. _helpContext))
      ]

transactionComposer ::
  forall p.
  State ->
  HTML p Action
transactionComposer state = case view (_marloweState <<< _Head <<< _executionState) state of
  SimulationNotStarted { initialSlot } ->
    div [ classes [ ClassName "transaction-composer", ClassName "composer" ] ]
      [ ul_
          [ h6
              [ classes
                  [ ClassName "input-composer-heading"
                  , noMargins
                  ]
              ]
              [ text "Simulation has not started yet" ]
          , div [ classes [ ClassName "slot-input", ClassName "initial-slot-input" ] ]
              [ spanText "Initial slot:"
              , marloweActionInput true (SetInitialSlot <<< wrap) initialSlot
              ]
          ]
      , div [ class_ (ClassName "transaction-btns") ]
          [ ul [ classes [ ClassName "demo-list", aHorizontal ] ]
              [ li [ classes [ bold, pointer ] ]
                  [ a [ onClick $ const $ Just StartSimulation ]
                      [ text "Start simulation" ]
                  ]
              ]
          ]
      ]
  SimulationRunning _ ->
    div [ classes [ ClassName "transaction-composer", ClassName "composer" ] ]
      [ ul [ class_ (ClassName "participants") ]
          if (Map.isEmpty possibleActions) then
            [ text "No valid inputs can be added to the transaction" ]
          else
            (actionsForParties possibleActions)
      , div [ class_ (ClassName "transaction-btns") ]
          [ ul [ classes [ ClassName "demo-list", aHorizontal ] ]
              [ li [ classes [ bold, pointer ] ]
                  [ a
                      [ onClick $ const
                          $ if hasHistory state then
                              Just Undo
                            else
                              Nothing
                      , class_ (Classes.disabled $ not isEnabled)
                      ]
                      [ text "Undo" ]
                  ]
              , li [ classes [ bold, pointer ] ]
                  [ a
                      [ onClick $ const
                          $ if hasHistory state then
                              Just ResetSimulator
                            else
                              Nothing
                      , class_ (Classes.disabled $ not isEnabled)
                      ]
                      [ text "Reset" ]
                  ]
              ]
          ]
      ]
  where
  isEnabled = isContractValid state

  possibleActions = view (_marloweState <<< _Head <<< _executionState <<< _SimulationRunning <<< _possibleActions <<< _Newtype) state

  kvs :: forall k v. Map k v -> Array (Tuple k v)
  kvs = Map.toUnfoldable

  vs :: forall k v. Map k v -> Array v
  vs m = map snd (kvs m)

  lastKey :: Maybe Party
  lastKey = map (\x -> x.key) (Map.findMax possibleActions)

  sortParties :: forall v. Array (Tuple Party v) -> Array (Tuple Party v)
  sortParties = sortWith (\(Tuple party _) -> party == otherActionsParty)

  actionsForParties :: Map Party (Map ActionInputId ActionInput) -> Array (HTML p Action)
  actionsForParties m = map (\(Tuple k v) -> participant state isEnabled k (vs v)) (sortParties (kvs m))

participant ::
  forall p.
  State ->
  Boolean ->
  Party ->
  Array ActionInput ->
  HTML p Action
participant state isEnabled party actionInputs =
  li [ classes [ ClassName "participant-a", noMargins ] ]
    ( [ h6_ [ em_ title ] ]
        <> (map (inputItem state isEnabled partyName) actionInputs)
    )
  where
  title =
    if party == otherActionsParty then
      [ text "Other Actions" ]
    else
      [ text "Participant ", strong_ [ text partyName ] ]

  partyName = case party of
    (PK name) -> name
    (Role name) -> name

inputItem ::
  forall p.
  State ->
  Boolean ->
  PubKey ->
  ActionInput ->
  HTML p Action
inputItem _ isEnabled person (DepositInput accountId party token value) =
  div [ classes [ aHorizontal ] ]
    [ p_ (renderDeposit accountId party token value)
    , div [ class_ (ClassName "align-top") ]
        [ button
            [ classes [ plusBtn, smallBtn, (Classes.disabled $ not isEnabled) ]
            , enabled isEnabled
            , onClick $ const $ Just
                $ AddInput (IDeposit accountId party token value) []
            ]
            [ text "+" ]
        ]
    ]

inputItem _ isEnabled person (ChoiceInput choiceId@(ChoiceId choiceName choiceOwner) bounds chosenNum) =
  div
    [ classes [ aHorizontal, ClassName "flex-wrap" ] ]
    ( [ div []
          [ p [ class_ (ClassName "choice-input") ]
              [ spanText "Choice "
              , b_ [ spanText (show choiceName <> ":") ]
              , br_
              , spanText "Choose value "
              , marloweActionInput isEnabled (SetChoice choiceId) chosenNum
              ]
          , p [ class_ (ClassName "choice-error") ] error
          ]
      ]
        <> addButton
    )
  where
  addButton =
    if isEnabled && inBounds chosenNum bounds then
      [ button
          [ classes [ plusBtn, smallBtn, ClassName "align-top" ]
          , onClick $ const $ Just
              $ AddInput (IChoice (ChoiceId choiceName choiceOwner) chosenNum) bounds
          ]
          [ text "+" ]
      ]
    else
      []

  error = if inBounds chosenNum bounds then [] else [ text boundsError ]

  boundsError =
    if Array.null bounds then
      "A choice must have set bounds, please fix the contract"
    else
      "Choice must be between " <> intercalate " or " (map boundError bounds)

  boundError (Bound from to) = show from <> " and " <> show to

inputItem _ isEnabled person NotifyInput =
  li
    [ classes [ ClassName "choice-a", aHorizontal ] ]
    [ p_ [ text "Notify Contract" ]
    , button
        [ classes [ plusBtn, smallBtn, (Classes.disabled $ not isEnabled), ClassName "align-top" ]
        , enabled isEnabled
        , onClick $ const $ Just
            $ AddInput INotify []
        ]
        [ text "+" ]
    ]

inputItem state isEnabled person (MoveToSlot slot) =
  div
    [ classes [ aHorizontal, ClassName "flex-wrap" ] ]
    ( [ div []
          [ p [ class_ (ClassName "slot-input") ]
              [ spanText "Move to slot "
              , marloweActionInput isEnabled (SetSlot <<< wrap) slot
              ]
          , p [ class_ (ClassName "choice-error") ] error
          ]
      ]
        <> addButton
    )
  where
  addButton =
    if isEnabled && inFuture state slot then
      [ button
          [ classes [ plusBtn, smallBtn, ClassName "align-top" ]
          , onClick $ const $ Just $ MoveSlot slot
          ]
          [ text "+" ]
      ]
    else
      []

  error = if inFuture state slot then [] else [ text boundsError ]

  boundsError = "The slot must be more than the current slot " <> (state ^. (_currentMarloweState <<< _executionState <<< _SimulationRunning <<< _slot <<< to show))

marloweActionInput :: forall p a. Show a => Boolean -> (BigInteger -> Action) -> a -> HTML p Action
marloweActionInput isEnabled f current =
  input
    [ type_ InputNumber
    , enabled isEnabled
    , placeholder "BigInteger"
    , class_ $ ClassName "action-input"
    , value $ show current
    , onValueChange
        $ ( \x ->
              Just
                $ f
                    ( case fromString x of
                        Just y -> y
                        Nothing -> fromInt 0
                    )
          )
    ]

renderDeposit :: forall p. AccountId -> Party -> Token -> BigInteger -> Array (HTML p Action)
renderDeposit accountOwner party tok money =
  [ spanText "Deposit "
  , b_ [ spanText (show money) ]
  , spanText " units of "
  , b_ [ spanText (showPrettyToken tok) ]
  , spanText " into Account "
  , b_ [ spanText (show accountOwner) ]
  , spanText " as "
  , b_ [ spanText (show party) ]
  ]
