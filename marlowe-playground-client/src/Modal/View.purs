module Modal.View
  ( modal
  ) where

import Data.Lens ((^.))
import Data.Maybe (Maybe(..))
import Demos.View (render) as Demos
import Effect.Aff.Class (class MonadAff)
import GistButtons (authButton)
import Halogen (ComponentHTML)
import Halogen.Classes (closeModal)
import Halogen.Extra (renderSubmodule)
import Halogen.HTML (ClassName(ClassName), div, img, text)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (class_, classes, src)
import MainFrame.Types (Action(..), ChildSlots, ModalView(..), State, _newProject, _projects, _rename, _saveAs, _showModal)
import NewProject.State (render) as NewProject
import Prelude (const, identity, ($))
import Projects.State (render) as Projects
import Rename.State (render) as Rename
import SaveAs.State (render) as SaveAs

modal ::
  forall m.
  MonadAff m =>
  State -> ComponentHTML Action ChildSlots m
modal state = case state ^. _showModal of
  Nothing -> text ""
  Just view ->
    div [ classes [ ClassName "overlay" ] ]
      [ div [ classes [ ClassName "modal" ] ]
          [ div [ class_ (ClassName "modal-close") ]
              [ img [ src closeModal, onClick $ const $ Just CloseModal ] ]
          , modalContent view
          ]
      ]
  where
  modalContent NewProject = renderSubmodule _newProject NewProjectAction NewProject.render state

  modalContent OpenProject = renderSubmodule _projects ProjectsAction Projects.render state

  modalContent OpenDemo = renderSubmodule identity DemosAction Demos.render state

  modalContent RenameProject = renderSubmodule _rename RenameAction Rename.render state

  modalContent SaveProjectAs = renderSubmodule _saveAs SaveAsAction SaveAs.render state

  modalContent (GithubLogin intendedAction) = authButton intendedAction state
