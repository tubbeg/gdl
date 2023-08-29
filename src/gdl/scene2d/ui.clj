(ns gdl.scene2d.ui
  (:require [x.x :refer [defmodule]]
            [gdl.lc :as lc]
            [gdl.files :as files]
            [gdl.graphics.batch :refer [batch]]
            [gdl.graphics.gui :as gui]
            [gdl.scene2d.actor :as actor])
  (:import com.badlogic.gdx.graphics.g2d.TextureRegion
           (com.badlogic.gdx.scenes.scene2d Stage Actor Group)
           (com.badlogic.gdx.scenes.scene2d.utils ChangeListener TextureRegionDrawable Drawable)
           (com.badlogic.gdx.scenes.scene2d.ui Table Skin TextButton CheckBox Window Button
            Button$ButtonStyle ImageButton ImageButton$ImageButtonStyle Label TooltipManager Tooltip
            TextTooltip TextField SplitPane Stack Image)
           (com.kotcrab.vis.ui VisUI VisUI$SkinScale)))

(defn actors [^Stage stage]
  (.getActors stage))

(defn- find-actor-with-id [stage id]
  (let [actors (actors stage)
        ids (keep actor/id actors)]
    (assert (apply distinct? ids)
            (str "Actor ids are not distinct: " (vec ids)))
    (first (filter #(= id (actor/id %))
                   actors))))

(defn- stage-ilookup [viewport batch]
  (proxy [Stage clojure.lang.ILookup] [viewport batch]
    (valAt
      ([id]
       (find-actor-with-id this id))
      ([id not-found]
       (or (find-actor-with-id this id)
           not-found)))))

(defn stage ^Stage []
  (stage-ilookup gui/viewport batch))

(defn draw-stage [stage]
  ; Not using (.draw ^Stage stage) because we are already managing
  ; .setProjectionMatrix / begin / end of batch and setting unit-scale in g/render-with
  ; https://github.com/libgdx/libgdx/blob/75612dae1eeddc9611ed62366858ff1d0ac7898b/gdx/src/com/badlogic/gdx/scenes/scene2d/Stage.java#L119
  ; https://github.com/libgdx/libgdx/blob/75612dae1eeddc9611ed62366858ff1d0ac7898b/gdx/src/com/badlogic/gdx/scenes/scene2d/Group.java#L56
  ; => use inside g/render-gui
  (.draw ^Group (.getRoot ^Stage stage)
         batch
         (float 1)))

(defn update-stage [stage delta]
  (.act ^Stage stage delta))

(defn mouseover? [^Stage stage]
  (let [[x y] (gui/mouse-position)]
    (.hit stage x y true)))

(declare ^Skin skin)

; TODO default skin not included in libgdx jar? check.
(defmodule _
  (lc/create [_]
    (.bindRoot #'skin (Skin. (files/internal "scene2d.ui.skin/uiskin.json")))
    (when-not (VisUI/isLoaded) ; app has error before VisUI/dispose and we call refresh-all
      (VisUI/load #_VisUI$SkinScale/X2)))
  (lc/dispose [_]
    (.dispose skin)
    (VisUI/dispose)))

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

(defn table ^Table []
  (Table.))

(defn text-button ^TextButton [text on-clicked]
  (let [button (TextButton. ^String text skin)]
    (.addListener button
                  (proxy [ChangeListener] []
                    (changed [event actor]
                      (on-clicked))))
    button))

(defn check-box ^CheckBox [text on-clicked checked?]
  (let [^Button button (CheckBox. ^String text skin)]
    (.setChecked button checked?)
    (.addListener button
                  (proxy [ChangeListener] []
                    (changed [event ^Button actor]
                      (on-clicked (.isChecked actor)))))
    button))

; TODO 'toggle' - imagebutton , :toggle true ?
(defn image-button ^ImageButton [{:keys [^TextureRegion texture] :as image} on-clicked]
  (let [style (ImageButton$ImageButtonStyle. ^Button$ButtonStyle (.get skin "toggle" Button$ButtonStyle))
        _ (set! (.imageUp   style) (TextureRegionDrawable. texture))
        _ (set! (.imageDown style) (TextureRegionDrawable. texture))
        ; imageChecked
        ; imageCheckedDown
       ; imageCheckedOver
        ; imageDisabled
        ; imageDown
        ; imageOver
        ; imageUp
        button (ImageButton. style)]
    (.addListener button
                  (proxy [ChangeListener] []
                    (changed [event actor]
                      (on-clicked))))
    button))

; https://stackoverflow.com/questions/29771114/how-can-i-add-button-to-top-right-corner-of-a-dialog-in-libgdx
; window with close button
(defn window ^Window [& {:keys [title modal?] :as opts}]
  (-> (doto (Window. ^String title skin)
        (.setModal (boolean modal?)))
      (actor/set-opts opts)))

(defn label ^Label [text]
  (Label. ^CharSequence text skin))

(defn text-field ^TextField [^String text]
  (TextField. text skin))

(defn actor ^Actor [actfn]
  (proxy [Actor] []
    (act [delta]
      (actfn))))

; TODO the tooltip manager sets my spritebatch color to 0.2 alpha for short time
; TODO also the widget where the tooltip is attached is flickering after
; the tooltip disappears
; => write your own manager without animations/time
(defn- instant-show-tooltip-manager ^TooltipManager [textfn]
  (let [manager (proxy [TooltipManager] []
                  (enter [^Tooltip tooltip]
                    (.setText ^Label (.getActor tooltip) ^String (textfn))
                    (.pack (.getContainer tooltip))
                    (let [^TooltipManager this this]
                      (proxy-super enter tooltip))))]
    (set! (.initialTime manager) 0)
    (set! (.resetTime   manager) 0)
    (set! (.animations  manager) false)
    (.hideAll manager)
    manager))

(defn text-tooltip ^TextTooltip [textfn]
  (TextTooltip. "" (instant-show-tooltip-manager textfn) skin))

(defn split-pane ^SplitPane [^Actor first-widget ^Actor second-widget ^Boolean vertical?]
  (SplitPane. first-widget second-widget vertical? skin))

(defn stack ^Stack []
  (Stack.))

(defn image ^Image [^Drawable drawable]
  (Image. drawable))
