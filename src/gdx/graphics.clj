(ns gdx.graphics
  (:require [clojure.string :refer [includes? split-lines upper-case]]
            [gdx.app :as app]
            [gdx.tiled :as tiled]
            [gdx.utils :refer [set-var-root]]
            [gdx.asset-manager :as asset-manager])
  (:import [java.io File]
           [com.badlogic.gdx Gdx Graphics]
           [com.badlogic.gdx.graphics GL20 OrthographicCamera Color Texture Pixmap Pixmap$Format]
           [com.badlogic.gdx.graphics.g2d Batch SpriteBatch TextureRegion]
           [com.badlogic.gdx.utils.viewport Viewport FitViewport]
           [com.badlogic.gdx.math Vector2 Circle Rectangle MathUtils]
           [space.earlygrey.shapedrawer ShapeDrawer]
           [com.badlogic.gdx.maps MapRenderer MapLayer]
           [gdx OrthogonalTiledMapRendererWithColorSetter ColorSetter]))

;(set! *unchecked-math* :warn-on-boxed) ; breaks (byte \char) at draw-string

(defn- ^Graphics graphics []
  (Gdx/graphics))

(defn fps []
  (.getFramesPerSecond (graphics)))

(def gui-unit-scale 1)
(declare world-unit-scale)

; set to 1 so we can query get-text-width on a text
; outside of rendering function at initialization
(def ^:private ^:dynamic *unit-scale* gui-unit-scale)

(declare ^:dynamic ^:private ^Batch *batch*) ; TODO no need for thread-binding just set-var-root.

(load "graphics/colors")
(load "graphics/shapes")
(load "graphics/images")
(load "graphics/text")

; TODO use proper naming gui- or world- (set-world-camera-position! ?)

; TODO somehow move world-camera/world-viewport out of here ?
; => gdx.world ?
; world/viewport-width
; gui/viewport-width
; or gui-viewport / world-viewport
; or gui inbuilt here and world extra
; (later)

(declare ^:private gui-camera
         gui-viewport
         ^:private ^OrthographicCamera world-camera
         ^:private world-viewport
         sprite-batch)

(app/on-create
  (set-var-root #'sprite-batch (SpriteBatch.))
  (create-shape-drawer sprite-batch)

  (set-var-root #'gui-camera (OrthographicCamera.))
  (set-var-root #'gui-viewport (FitViewport. (.getWidth (graphics)) (.getHeight (graphics)) gui-camera))

  ; important ! create after world-unit-scale so font images have :world-unit-dimensions set
  (create-font)

  (set-var-root #'world-camera (OrthographicCamera.))
  (let [width  (* (.getWidth (graphics))  world-unit-scale)
        height (* (.getHeight (graphics)) world-unit-scale)]
    (.setToOrtho world-camera false width height)
    (set-var-root #'world-viewport (FitViewport. width height world-camera))))

(def ^:private world-camera-position (atom nil))

(defn camera-position []
  @world-camera-position)

(defn set-camera-position! [position]
  (reset! world-camera-position position))

(defn on-resize [w h]
  (.update gui-viewport w h true)
  (.update world-viewport w h true))

(defn- fix-viewport-update
  "Sometimes the viewport update is not triggered."
  []
  (let [screen-width  (.getWidth  (graphics))
        screen-height (.getHeight (graphics))]
    (if (or (not= (.getScreenWidth  gui-viewport) screen-width)
            (not= (.getScreenHeight gui-viewport) screen-height))
      (on-resize screen-width screen-height))))

(defn on-update []
  (fix-viewport-update))

(app/on-destroy
 (.dispose sprite-batch)
 (dispose-shape-drawer))

; TODO use below.
(defmacro with-gui-bindings [& exprs]
  `(binding [*batch* sprite-batch
             *unit-scale* gui-unit-scale]
     (set-shape-drawer-default-line-width 1)
     ~@exprs))

(defn- render-with [batch unit-scale ^OrthographicCamera camera renderfn]
  (binding [*batch* batch
            *unit-scale* unit-scale]
    (set-shape-drawer-default-line-width 1)
    (.setProjectionMatrix *batch* (.combined camera))
    (.begin *batch*)
    (renderfn)
    (.end *batch*)))

; TODO use partial., no need to pass sprite-batch
(defn render-gui-level [renderfn]
  (.setColor sprite-batch white)
  (render-with sprite-batch gui-unit-scale gui-camera renderfn))

(defn render-map-level [renderfn]
  #_(when-not (= white (.getColor sprite-batch))
    (println "render map level spritebatch color: "
             [(.r (.getColor sprite-batch))
              (.g (.getColor sprite-batch))
              (.b (.getColor sprite-batch))
              (.a (.getColor sprite-batch))

              ]

             ))
  (.setColor sprite-batch white)
  (render-with sprite-batch world-unit-scale world-camera renderfn))

; OrthogonalTiledMapRenderer extends BatchTiledMapRenderer
; and when a batch is passed to the constructor
; we do not need to dispose the renderer
(defn- map-renderer-for [tiled-map color-setter]
  (OrthogonalTiledMapRendererWithColorSetter. tiled-map
                                              (float world-unit-scale)
                                              sprite-batch
                                              (reify ColorSetter
                                                (apply [_ color x y]
                                                  (color-setter color x y)))))

(def ^:private cached-map-renderer (memoize map-renderer-for))

(defn render-map [tiled-map color-setter]
  (set! (.x (.position world-camera)) (@world-camera-position 0))
  (set! (.y (.position world-camera)) (@world-camera-position 1))
  (.update world-camera)
  (let [^MapRenderer map-renderer (cached-map-renderer tiled-map color-setter)]
    (.setView map-renderer world-camera)
    (->> tiled-map
         tiled/layers
         (filter #(.isVisible ^MapLayer %))
         (map (partial tiled/layer-index tiled-map))
         int-array
         (.render map-renderer))))

(defn- clamp [value min max]
  (MathUtils/clamp (float value) (float min) (float max)))

; touch coordinates are y-down, while screen coordinates are y-up
; so the clamping of y is reverse, but as black bars are equal it does not matter
(defn- unproject-mouse-posi [^Viewport viewport]
  (let [mouse-x (clamp (.getX (Gdx/input))
                       (.getLeftGutterWidth viewport)
                       (.getRightGutterX viewport))
        mouse-y (clamp (.getY (Gdx/input))
                       (.getTopGutterHeight viewport)
                       (.getTopGutterY viewport))
        coords (.unproject viewport (Vector2. mouse-x mouse-y))]
    [(.x coords) (.y coords)]))

; -> no-doc here and @ input mouse-position / world-mouse-position ?

; TODO gui-mouse-position!
(defn mouse-coords []
  (mapv int (unproject-mouse-posi gui-viewport)))

; TODO world-mouse-position!
(defn map-coords
  "Can be negative coordinates, undefined cells." ; TODO check if true
  []
  (unproject-mouse-posi world-viewport))

(defn ^:no-doc clear-screen [] ; TODO use clear screen utils
  (.glClearColor (Gdx/gl) 0 0 0 1)
  (.glClear (Gdx/gl) GL20/GL_COLOR_BUFFER_BIT))

(defn viewport-width  [] (.getWorldWidth  gui-viewport))
(defn viewport-height [] (.getWorldHeight gui-viewport))

(defn world-viewport-width  [] (.getWorldWidth  world-viewport))
(defn world-viewport-height [] (.getWorldHeight world-viewport))

(defn world-frustum []
  (let [frustum-points (for [point (take 4 (.planePoints (.frustum world-camera)))
                             :let [x (.x point)
                                   y (.y point)]]
                         [x y])
        left-x   (apply min (map first  frustum-points))
        right-x  (apply max (map first  frustum-points))
        bottom-y (apply min (map second frustum-points))
        top-y    (apply max (map second frustum-points))]
    ; rectangle :
    #_{:left-bottom x
       :width  viewport-width camera
       :height viewport-height camera}
    [left-x right-x bottom-y top-y]
    ))

(defn visible-tiles []
  (let [[left-x right-x bottom-y top-y] (world-frustum)]
    (for  [x (range (int left-x)   (int right-x))
           y (range (int bottom-y) (+ 2 (int top-y)))]
      [x y])))
