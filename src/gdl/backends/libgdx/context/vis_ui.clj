(ns gdl.backends.libgdx.context.vis-ui
  (:require [gdl.app :refer [current-context]]
            gdl.context
            gdl.disposable
            gdl.scene2d.ui)
  (:import com.badlogic.gdx.Gdx
           com.badlogic.gdx.graphics.g2d.TextureRegion
           com.badlogic.gdx.scenes.scene2d.Actor
           (com.badlogic.gdx.scenes.scene2d.ui Skin Button TooltipManager Tooltip TextTooltip Label)
           (com.badlogic.gdx.scenes.scene2d.utils ChangeListener TextureRegionDrawable)
           (com.kotcrab.vis.ui VisUI VisUI$SkinScale)
           (com.kotcrab.vis.ui.widget VisTextButton VisCheckBox VisImageButton)))

(defn ->context []
  ; app crashes during startup before VisUI/dispose and we do clojure.tools.namespace.refresh-> gui elements not showing.
  ; => actually there is a deeper issue at play
  ; we need to dispose ALL resources which were loaded already ...
  (when (VisUI/isLoaded)
    (VisUI/dispose))
  (VisUI/load #_VisUI$SkinScale/X2) ; TODO skin-scale arg

  ; this is the gdx default skin  - copied from libgdx project, check not included in libgdx jar somewhere?
  {:context.ui/default-skin (Skin. (.internal Gdx/files "scene2d.ui.skin/uiskin.json"))
   :context/vis-ui (reify gdl.disposable/Disposable
                     (dispose [_]
                       (VisUI/dispose)))})

(comment
 ; TODO set custom font with default skin - or set custom skin param
 ; https://stackoverflow.com/questions/45523878/libgdx-skin-not-updating-when-changing-font-programmatically
 (let [empty-skin (Skin.)]
   (.add skin "font" my-font)
   ; skin.addRegion(new TextureAtlas(Gdx.files.internal("mySkin.atlas")));
   ; skin.load(Gdx.files.internal("mySkin.json"));
   ; TODO will this overload 'default-font' ?
   ; => I need to pass my custom skin to gdl.ui !
   ; then, in your JSON file you can reference “font”
   ;
   ; {
   ;   font: font
   ; }
   ))

; TODO add Actor/Widget, also using current-context & tooltips

(defn- ->change-listener [_ on-clicked]
  (proxy [ChangeListener] []
    (changed [event actor] ; TODO pass also event / actor as event/event event/actor or something
      (on-clicked @current-context))))
; TODO this could do (swap! current-context on-clicked) ??
; => all change-screens could be done pure functions o.o / hide / enter 'pure' functions

; TODO the tooltip manager sets my spritebatch color to 0.2 alpha for short time
; TODO also the widget where the tooltip is attached is flickering after
; the tooltip disappears
; => write your own manager without animations/time
(defn- instant-show-tooltip-manager ^TooltipManager [textfn]
  (let [manager (proxy [TooltipManager] []
                  (enter [^Tooltip tooltip]
                    (.setText ^Label (.getActor tooltip) ^String (textfn @current-context))
                    (.pack (.getContainer tooltip))
                    (let [^TooltipManager this this]
                      (proxy-super enter tooltip))))]
    (set! (.initialTime manager) 0)
    (set! (.resetTime   manager) 0)
    (set! (.animations  manager) false)
    (.hideAll manager)
    manager))

(extend-type gdl.context.Context
  gdl.context/Widgets
  (->actor [_ {:keys [draw act]}]
    (proxy [Actor] []
      (draw [_batch _parent-alpha]
        (when draw
          (draw @current-context)))
      (act [delta]
        (when act
          (act @current-context)))))

  ; ^TextButton
  (->text-button [context text on-clicked]
    (let [button (VisTextButton. ^String text)]
      (.addListener button (->change-listener context on-clicked))
      button))

  ; ^CheckBox
  (->check-box [context text on-clicked checked?]
    (let [^Button button (VisCheckBox. ^String text)]
      (.setChecked button checked?)
      (.addListener button
                    (proxy [ChangeListener] []
                      (changed [event ^Button actor]
                        (on-clicked (.isChecked actor)))))
      button))

  ; TODO give directly texture-region
  ; TODO check how to make toggle-able ? with hotkeys for actionbar trigger ?
  ; ^VisImageButton
  (->image-button [context image on-clicked]
    (let [button (VisImageButton. (TextureRegionDrawable. ^TextureRegion (:texture image)))]
      (.addListener button (->change-listener context on-clicked))
      button))

  ; TODO VisToolTip
  ; https://github.com/kotcrab/vis-ui/wiki/Tooltips
  (->text-tooltip ^TextTooltip [{:keys [context.ui/default-skin]} textfn]
    (TextTooltip. "" (instant-show-tooltip-manager textfn) ^Skin default-skin))
  )
