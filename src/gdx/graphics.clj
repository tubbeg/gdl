(ns gdx.graphics
  (:require [clojure.string :as str]
            [gdx.app :as app]
            [gdx.graphics.color :as color]
            [gdx.graphics.shape-drawer :as shape-drawer])
  (:import [com.badlogic.gdx Gdx Graphics]
           com.badlogic.gdx.utils.Align
           [com.badlogic.gdx.graphics OrthographicCamera]
           [com.badlogic.gdx.graphics.g2d Batch SpriteBatch BitmapFont]
           [com.badlogic.gdx.utils.viewport Viewport FitViewport]
           [com.badlogic.gdx.math Vector2 Vector3 MathUtils]))

(app/defmanaged ^:no-doc ^Graphics graphics Gdx/graphics)

; TODO frames-per-second
(defn fps [] (.getFramesPerSecond graphics))

(defn- screen-width
  "note: this is not the viewport-width, which may be different than the screen-width"
  []
  (.getWidth  graphics))

(defn- screen-height
  "note: this is not the viewport-height, which may be different than the screen-height."
  []
  (.getHeight graphics))

(def ^:no-doc gui-unit-scale 1) ; => pixel-unit-scale
(def world-unit-scale 1)

; -> *unit-scale* is bound to :wu or :px
; and world-unit-scale
; or pixels->world-units is all thats needed
; no gui-unit-scale

(defn pixels->world-units [px]
  (* px world-unit-scale))

(def ^:no-doc ^:dynamic *unit-scale*)

(app/defmanaged ^:no-doc ^:dispose ^Batch batch (SpriteBatch.))

(app/on-create
 (shape-drawer/create batch))

(app/defmanaged ^:no-doc ^:dispose ^BitmapFont default-font (BitmapFont.))

; TODO what if wrong name/doesnt exist? check ?
#_(use 'clojure.pprint)
#_(clojure.pprint/pprint
   (com.badlogic.gdx.graphics.Colors/getColors))

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

;https://javadoc.io/static/com.badlogicgames.gdx/gdx/1.11.0/com/badlogic/gdx/graphics/g2d/BitmapFontCache.html#addText-java.lang.CharSequence-float-float-int-int-float-int-boolean-java.lang.String-

;; ****
;; **** getting height/width of text with glyphlayout :::
;
; BitmapFont font;
; SpriteBatch spriteBatch;
; //... Load any font of your choice first
; FreeTypeFontGenerator fontGenerator = new FreeTypeFontGenerator(
;    Gdx.files.internal("myFont.ttf")
; );
; FreeTypeFontGenerator.FreeTypeFontParameter freeTypeFontParameter =
;       new FreeTypeFontGenerator.FreeTypeFontParameter();
; freeTypeFontParameter.size = size;
; fontGenerator.generateData(freeTypeFontParameter);
; font = fontGenerator.generateFont(freeTypeFontParameter);
;
; //Initialize the spriteBatch as requirement
;
; GlyphLayout glyphLayout = new GlyphLayout();
; String item = "Example";
; glyphLayout.setText(font,item);
; float w = glyphLayout.width;
; font.draw(spriteBatch, glyphLayout, (Game.SCREEN_WIDTH - w)/2, y);
;
;; ****
;; ****

; TODO ?
; gdx.graphics.views.world / *.gui

; => unit-scale, camera, viewport, etc.

(app/defmanaged ^:private ^OrthographicCamera   gui-camera (OrthographicCamera.))
(app/defmanaged ^:no-doc  ^OrthographicCamera world-camera (OrthographicCamera.))

; TODO use extend viewport ???

; => TODO this is screen-viewport ? == same like screen ?
; screen-camera always pointed at center of screen !!
(app/defmanaged ^:no-doc ^Viewport gui-viewport
  (FitViewport. (screen-width)
                (screen-height)
                gui-camera))

(app/defmanaged ^:private ^Viewport world-viewport
  (let [width  (* (screen-width)  world-unit-scale)
        height (* (screen-height) world-unit-scale)
        y-down? false]
    (.setToOrtho world-camera y-down? width height)
    (FitViewport. width
                  height
                  world-camera)))

(def ^:private world-camera-position (atom nil))

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
