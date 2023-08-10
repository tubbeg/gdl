(ns gdl.ui
  (:require [x.x :refer [defcomponent]]
            [gdl.lc :as lc]
            [gdl.files :as files]
            [gdl.graphics :as g]
            [gdl.graphics.batch :refer [batch]]
            [gdl.graphics.gui :as gui])
  (:import [com.badlogic.gdx.graphics.g2d TextureRegion]
           [com.badlogic.gdx.scenes.scene2d Stage Actor
            Group]
           [com.badlogic.gdx.scenes.scene2d.utils ChangeListener TextureRegionDrawable]
           [com.badlogic.gdx.scenes.scene2d.ui Table Skin TextButton CheckBox Window
            Button Button$ButtonStyle ImageButton ImageButton$ImageButtonStyle
            Label TooltipManager Tooltip TextTooltip]))

; TODO constructor fns type hint for result -> no reflection @ game.*
; => check @ game.* reflection warnings too... !

; separate scene2d (stage,actor ) & ui ?

(defn stage ^Stage []
  (Stage. gui/viewport batch))


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

(declare ^Skin skin)

; TODO default skin not included in libgdx jar? check.
(defcomponent *ns* _
  (lc/create [_]
    (.bindRoot #'skin (Skin. (files/internal "scene2d.ui.skin/uiskin.json"))))
  (lc/dispose [_]
    (.dispose skin)))

; https://stackoverflow.com/questions/45523878/libgdx-skin-not-updating-when-changing-font-programmatically

(defn table ^Table []
  (Table.))

; TODO Button implements disposable??
; TODO how to check any objects disposable interface and I didnt dispose?

; TODO do I have to pass .get skin class this or can i pass directly skin?? try.

(defn text-button ^TextButton [text on-clicked]
  (let [button (TextButton. ^String text skin)]
    (.addListener button
                  (proxy [ChangeListener] []
                    (changed [event actor]
                      (on-clicked))))
    button))

(defn check-box [text on-clicked checked?]
  (let [^Button button (CheckBox. ^String text skin)]
    (.setChecked button checked?)
    (.addListener button
                  (proxy [ChangeListener] []
                    (changed [event ^Button actor]
                      (on-clicked (.isChecked actor)))))
    button))

; TODO 'toggle' - imagebutton , :toggle true ?
(defn image-button [{:keys [^TextureRegion texture] :as image} on-clicked]
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
(defn window [title]
  (Window. ^String title skin))

(defn label [text]
  (Label. ^CharSequence text skin))

(defn actor [actfn]
  (proxy [Actor] []
    (act [delta]
      (actfn))))

; TODO the tooltip manager sets my spritebatch color to 0.2 alpha for short time !!
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

(defn text-tooltip [textfn]
  (TextTooltip. "" (instant-show-tooltip-manager textfn) skin))
