(declare ^:private ^ShapeDrawer shape-drawer)

(let [shape-drawer-texture (atom nil)]

  (defn- create-shape-drawer [batch]
    (let [pixmap (doto (Pixmap. 1 1 Pixmap$Format/RGBA8888)
                   (.setColor Color/WHITE)
                   (.drawPixel 0 0))
          texture (Texture. pixmap)
          _ (.dispose pixmap)
          region (TextureRegion. texture 0 0 1 1)]
      (reset! shape-drawer-texture texture)
      (set-var-root #'shape-drawer (ShapeDrawer. batch region))))

  (defn- dispose-shape-drawer []
    (.dispose @shape-drawer-texture)))

(defn- set-color
  "For shape drawer."
  [^Color color]
  (.setColor shape-drawer color))

(defn set-shape-drawer-default-line-width [scale] ; TODO do this * unit-scale at binding render-with
  (.setDefaultLineWidth shape-drawer (float (* scale *unit-scale*))))

(defmacro with-shape-drawer-line-width [width & body]
  `(do
    (set-shape-drawer-default-line-width ~width)
    ~@body
    (set-shape-drawer-default-line-width 1)))

(defn draw-ellipse [[x y] radius-x radius-y color]
  (set-color color)
  (.ellipse shape-drawer (float x) (float y) (float radius-x) (float radius-y)))

(defn fill-ellipse [[x y] radius-x radius-y color]
  (set-color color)
  (.filledEllipse shape-drawer (float x) (float y) (float radius-x) (float radius-y)))

(defn draw-circle [[x y] radius color]
  (set-color color)
  (.circle shape-drawer (float x) (float y) (float radius)))

(defn fill-circle [[x y] radius color]
  (set-color color)
  (.filledCircle shape-drawer (float x) (float y) (float radius)))

(defn- degree->radians [degree]
  (* degree (/ (Math/PI) 180)))

(defn draw-arc [[centre-x centre-y] radius start-angle degree color]
  (set-color color)
  (.arc shape-drawer centre-x centre-y radius start-angle (degree->radians degree)))

(defn draw-sector [[centre-x centre-y] radius start-angle degree color]
  (set-color color)
  (.sector shape-drawer centre-x centre-y radius start-angle (degree->radians degree)))

(defn draw-rect
  ([[x y w h] color]
   (draw-rect x y w h color))
  ([x y w h color]
   (set-color color)
   (.rectangle shape-drawer x y w h)))

(defn fill-rect
  ([[x y w h] color]
   (fill-rect x y w h color))
  ([x y w h color]
   (set-color color)
   (.filledRectangle shape-drawer (float x) (float y) (float w) (float h))))

(defn draw-line
  ([[x y] [ex ey] color]
   (draw-line x y ex ey color))
  ([x y ex ey color]
   (set-color color)
   (.line shape-drawer (float x) (float y) (float ex) (float ey))))

(defn draw-grid
  [leftx bottomy gridw gridh cellw cellh color]
  (let [w (* gridw cellw)
        h (* gridh cellh)
        topy (+ bottomy h)
        rightx (+ leftx w)]
    (doseq [idx (range (inc gridw))
            :let [linex (+ leftx (* idx cellw))]]
           (draw-line linex topy linex bottomy color))
    (doseq [idx (range (inc gridh))
            :let [liney (+ bottomy (* idx cellh))]]
           (draw-line leftx liney rightx liney color))))
