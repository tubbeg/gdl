(declare ^:no-doc ^ShapeDrawer shape-drawer)

(let [shape-drawer-texture (atom nil)]

  (app/on-create
   (let [pixmap (doto (Pixmap. 1 1 Pixmap$Format/RGBA8888)
                  (.setColor Color/WHITE)
                  (.drawPixel 0 0))
         texture (Texture. pixmap)
         _ (.dispose pixmap)
         region (TextureRegion. texture 0 0 1 1)]
     (reset! shape-drawer-texture texture)
     (set-var-root #'shape-drawer (ShapeDrawer. batch region))))

  (app/on-destroy
   (.dispose ^Texture @shape-drawer-texture)))

(defn- set-shapes-color [^Color color]
  (.setColor shape-drawer color))

(defn ^:no-doc set-default-line-width [width]
  (.setDefaultLineWidth shape-drawer (float width)))

(defn ^:no-doc set-shape-drawer-unit-scale []
  (set-default-line-width *unit-scale*))

(defmacro with-shape-drawer-line-width [width & exprs]
  `(let [old-line-width# (.getDefaultLineWidth shape-drawer)]
     (set-default-line-width (* ~width old-line-width#))
     ~@exprs
     (set-default-line-width old-line-width#)))

(defn draw-ellipse [[x y] radius-x radius-y color]
  (set-shapes-color color)
  (.ellipse shape-drawer (float x) (float y) (float radius-x) (float radius-y)))

(defn fill-ellipse [[x y] radius-x radius-y color]
  (set-shapes-color color)
  (.filledEllipse shape-drawer (float x) (float y) (float radius-x) (float radius-y)))

(defn draw-circle [[x y] radius color]
  (set-shapes-color color)
  (.circle shape-drawer (float x) (float y) (float radius)))

(defn fill-circle [[x y] radius color]
  (set-shapes-color color)
  (.filledCircle shape-drawer (float x) (float y) (float radius)))

(defn- degree->radians [degree]
  (* degree (/ (Math/PI) 180)))

(defn draw-arc [[centre-x centre-y] radius start-angle degree color]
  (set-shapes-color color)
  (.arc shape-drawer centre-x centre-y radius start-angle (degree->radians degree)))

(defn draw-sector [[centre-x centre-y] radius start-angle degree color]
  (set-shapes-color color)
  (.sector shape-drawer centre-x centre-y radius start-angle (degree->radians degree)))

(defn draw-rect
  ([[x y w h] color]
   (draw-rect x y w h color))
  ([x y w h color]
   (set-shapes-color color)
   (.rectangle shape-drawer x y w h)))

(defn fill-rect
  ([[x y w h] color]
   (fill-rect x y w h color))
  ([x y w h color]
   (set-shapes-color color)
   (.filledRectangle shape-drawer (float x) (float y) (float w) (float h))))

(defn draw-line
  ([[x y] [ex ey] color]
   (draw-line x y ex ey color))
  ([x y ex ey color]
   (set-shapes-color color)
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
