(ns gdx.graphics
  (:require [clojure.string :refer (upper-case)]
            [gdx.app :as app]
            [gdx.asset-manager :as asset-manager])
  (:import [com.badlogic.gdx Gdx Graphics]
           [com.badlogic.gdx.graphics OrthographicCamera Color Texture Pixmap Pixmap$Format]
           [com.badlogic.gdx.graphics.g2d Batch SpriteBatch TextureRegion BitmapFont]
           [com.badlogic.gdx.utils.viewport Viewport FitViewport]
           [com.badlogic.gdx.math Vector2 Vector3 MathUtils]
           [space.earlygrey.shapedrawer ShapeDrawer]))

(app/defmanaged ^Graphics graphics Gdx/graphics)

(defn fps [] (.getFramesPerSecond graphics))

(defn screen-width  [] (.getWidth  graphics))
(defn screen-height [] (.getHeight graphics))

(def gui-unit-scale   1)
(def world-unit-scale 1)

(defn pixels->world-units [px]
  (* px world-unit-scale))

(def ^:dynamic *unit-scale*)

(app/defmanaged ^{:tag Batch :dispose true} batch (SpriteBatch.))

(load "graphics/colors")
(load "graphics/shapes")
(load "graphics/images")

(app/defmanaged ^{:tag BitmapFont :dispose true} default-font (BitmapFont.))

(defn draw-text [text x y]
  (.draw default-font batch ^String text (float x) (float y)))

(app/defmanaged ^OrthographicCamera   gui-camera (OrthographicCamera.))
(app/defmanaged ^OrthographicCamera world-camera (OrthographicCamera.))

(app/defmanaged ^Viewport gui-viewport
  (FitViewport. (screen-width)
                (screen-height)
                gui-camera))

(app/defmanaged ^Viewport world-viewport
  (let [width  (* (screen-width)  world-unit-scale)
        height (* (screen-height) world-unit-scale)
        y-down false]
    (.setToOrtho world-camera y-down width height)
    (FitViewport. width
                  height
                  world-camera)))

(def ^:private world-camera-position (atom nil))

(defn camera-position []
  @world-camera-position)

(defn set-camera-position! [position]
  (reset! world-camera-position position))

(defn update-world-camera-position []
  (set! (.x (.position world-camera)) (@world-camera-position 0))
  (set! (.y (.position world-camera)) (@world-camera-position 1))
  (.update world-camera))

(defn on-resize [w h]
  (let [center-camera? true]
    (.update gui-viewport   w h center-camera?)
    (.update world-viewport w h center-camera?)))

(defn fix-viewport-update
  "Sometimes the viewport update is not triggered."
  []
  (when-not (and (= (.getScreenWidth  gui-viewport) (screen-width))
                 (= (.getScreenHeight gui-viewport) (screen-height)))
    (on-resize (screen-width) (screen-height))))

(defn- render-with [unit-scale ^OrthographicCamera camera renderfn]
  (binding [*unit-scale* unit-scale]
    (set-shape-drawer-unit-scale)
    (.setColor batch white) ; fix scene2d.ui.tooltip flickering
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

; TODO gui-mouse-position!
(defn mouse-coords []
  (mapv int (unproject-mouse-posi gui-viewport)))

; TODO world-mouse-position!
(defn map-coords
  "Can be negative coordinates, undefined cells." ; TODO check if true
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
