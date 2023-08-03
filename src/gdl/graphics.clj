(ns gdl.graphics
  (:require [clojure.string :as str]
            [gdl.utils :refer :all]
            [gdl.graphics.color :as color]
            [gdl.graphics.shape-drawer :as shape-drawer])
  (:import [com.badlogic.gdx Gdx Graphics]
           com.badlogic.gdx.utils.Align
           [com.badlogic.gdx.graphics OrthographicCamera]
           [com.badlogic.gdx.graphics.g2d Batch SpriteBatch BitmapFont]
           [com.badlogic.gdx.utils.viewport Viewport FitViewport]
           [com.badlogic.gdx.math Vector2 Vector3 MathUtils]))

(declare ^:no-doc ^Graphics graphics
         ^:no-doc ^Batch batch

         ^:no-doc ^:dynamic *unit-scale*

         ^:no-doc gui-unit-scale
         world-unit-scale

         ^:no-doc ^BitmapFont default-font

         ^:private ^OrthographicCamera   gui-camera
         ^:no-doc  ^OrthographicCamera world-camera

         ^:no-doc  ^Viewport   gui-viewport
         ^:private ^Viewport world-viewport)

(defn- screen-width  [] (.getWidth  graphics))
(defn- screen-height [] (.getHeight graphics))

(defn load-state [{:keys [gui-unit-scale world-unit-scale]}]
  (set-var-root #'graphics Gdx/graphics)

  (set-var-root #'batch (SpriteBatch.))

  (set-var-root   #'gui-unit-scale   gui-unit-scale)
  (set-var-root #'world-unit-scale world-unit-scale)

  ; TODO doesnt work in world scale.
  (set-var-root #'default-font (BitmapFont.))

  (set-var-root #'gui-camera   (OrthographicCamera.))
  (set-var-root #'world-camera (OrthographicCamera.))

  (set-var-root #'gui-viewport (FitViewport. (screen-width)
                                             (screen-height)
                                             gui-camera))

  (set-var-root #'world-viewport (let [width  (* (screen-width)  world-unit-scale)
                                       height (* (screen-height) world-unit-scale)
                                       y-down? false]
                                   (.setToOrtho world-camera y-down? width height)
                                   (FitViewport. width
                                                 height
                                                 world-camera)))

  (shape-drawer/load-state batch))

(defn dispose-state []
  (dispose batch)
  (dispose default-font)
  (shape-drawer/dispose-state))

; TODO frames-per-second
(defn fps [] (.getFramesPerSecond graphics))

(defn pixels->world-units [px]
  (* px world-unit-scale))

; 1. check colors if missing/wrong
#_(use 'clojure.pprint)
#_(clojure.pprint/pprint
   (com.badlogic.gdx.graphics.Colors/getColors))
; 2. add new colors & fix in cdq all g/draw-text occurences
; (where more fat font, more border (dmg/hp) and colors, etc...
; (adjust graphics.freetype to add color/border/bordercolor)
; 3. add font to scene2d skin ui

(defn- text-height [^BitmapFont font text]
  (-> text
      (str/split #"\n")
      count
      (* (.getLineHeight font))))

; not sure is a problem (performance) to setScale
; at every draw-text
; could cache it @ font or somewhere for each unit-scale or not even set it back
(defn draw-text [{:keys [font text x y h-align up?]}]
  (let [^BitmapFont font (or font default-font)
        data (.getData font)
        old-scale (.scaleX data)]
    ; background -> get width from glyphlayout only (not necessary yet)
    ;(shape-drawer/filled-rectangle 270 177 250 height color/gray)
    (.setScale data (float (* old-scale *unit-scale*)))
    (.draw font
           batch
           (str text)
           (float x)
           (float (+ y (if up? (text-height font text) 0)))
           (float 0) ; target-width
           (case (or h-align :center)
             :center Align/center
             :left   Align/left
             :right  Align/right)
           false) ; wrap false, no need target-width
    (.setScale data (float old-scale))))

;; **** getting height/width of text with glyphlayout :::
;
; GlyphLayout glyphLayout = new GlyphLayout();
; String item = "Example";
; glyphLayout.setText(font,item);
; float w = glyphLayout.width;
; font.draw(spriteBatch, glyphLayout, (Game.SCREEN_WIDTH - w)/2, y);
;
;; ****

(def ^:private world-camera-position (atom nil)) ; TODO state?

; TODO world-
(defn camera-position [] @world-camera-position)

; TODO world-
(defn set-camera-position! [position]
  (reset! world-camera-position position))

(defn ^:no-doc update-world-camera-position []
  (set! (.x (.position world-camera)) (@world-camera-position 0))
  (set! (.y (.position world-camera)) (@world-camera-position 1))
  (.update world-camera))

(defn ^:no-doc on-resize [w h]
  (let [center-camera? true]
    (.update gui-viewport   w h center-camera?)
    (.update world-viewport w h center-camera?)))

(defn ^:no-doc fix-viewport-update
  "Sometimes the viewport update is not triggered."
  []
  (when-not (and (= (.getScreenWidth  gui-viewport) (screen-width))
                 (= (.getScreenHeight gui-viewport) (screen-height)))
    (on-resize (screen-width) (screen-height))))

(defn- render-with [unit-scale ^OrthographicCamera camera renderfn]
  (binding [*unit-scale* unit-scale]
    (shape-drawer/set-line-width! *unit-scale*)
    (.setColor batch color/white) ; fix scene2d.ui.tooltip flickering
    (.setProjectionMatrix batch (.combined camera))
    (.begin batch)
    (renderfn)
    (.end batch)))

(defn render-gui   [renderfn] (render-with   gui-unit-scale   gui-camera renderfn))
(defn render-world [renderfn] (render-with world-unit-scale world-camera renderfn))

(defn- clamp [value min max]
  (MathUtils/clamp (float value) (float min) (float max)))

; touch coordinates are y-down, while screen coordinates are y-up
; so the clamping of y is reverse, but as black bars are equal it does not matter
(defn- unproject-mouse-posi [^Viewport viewport]
  (let [mouse-x (clamp (.getX Gdx/input)
                       (.getLeftGutterWidth viewport)
                       (.getRightGutterX viewport))
        mouse-y (clamp (.getY Gdx/input)
                       (.getTopGutterHeight viewport)
                       (.getTopGutterY viewport))
        coords (.unproject viewport (Vector2. mouse-x mouse-y))]
    [(.x coords) (.y coords)]))

; TODO mouse-position
(defn mouse-coords []
  (mapv int (unproject-mouse-posi gui-viewport)))

; TODO world-mouse-position
; TODO clamping only works for gui-viewport ? check. comment if true
(defn map-coords
  "Can be negative coordinates, undefined cells."
  []
  (unproject-mouse-posi world-viewport))

(defn viewport-width  [] (.getWorldWidth  gui-viewport))
(defn viewport-height [] (.getWorldHeight gui-viewport))

(defn world-viewport-width  [] (.getWorldWidth  world-viewport))
(defn world-viewport-height [] (.getWorldHeight world-viewport))

(defn world-frustum []
  (let [frustum-points (for [^Vector3 point (take 4 (.planePoints (.frustum world-camera)))
                             :let [x (.x point)
                                   y (.y point)]]
                         [x y])
        left-x   (apply min (map first  frustum-points))
        right-x  (apply max (map first  frustum-points))
        bottom-y (apply min (map second frustum-points))
        top-y    (apply max (map second frustum-points))]
    [left-x right-x bottom-y top-y]))

(defn visible-tiles []
  (let [[left-x right-x bottom-y top-y] (world-frustum)]
    (for  [x (range (int left-x)   (int right-x))
           y (range (int bottom-y) (+ 2 (int top-y)))]
      [x y])))
