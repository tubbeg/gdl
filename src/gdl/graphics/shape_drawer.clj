(ns gdl.graphics.shape-drawer
  (:import [com.badlogic.gdx.graphics Texture Pixmap Pixmap$Format Color]
           com.badlogic.gdx.graphics.g2d.TextureRegion
           space.earlygrey.shapedrawer.ShapeDrawer))

(defn gen-drawer-texture ^Texture []
  (let [pixmap (doto (Pixmap. 1 1 Pixmap$Format/RGBA8888)
                 (.setColor Color/WHITE)
                 (.drawPixel 0 0))
        texture (Texture. pixmap)]
    (.dispose pixmap)
    texture))

(defn ->shape-drawer [batch ^Texture texture]
  (ShapeDrawer. batch (TextureRegion. texture 0 0 1 1)))

(defmacro with-line-width [drawer width & exprs]
  (let [drawer (vary-meta drawer assoc :tag 'space.earlygrey.shapedrawer.ShapeDrawer)]
    `(let [old-line-width# (.getDefaultLineWidth ~drawer)]
       (.setDefaultLineWidth ~drawer (float (* ~width old-line-width#)))
       ~@exprs
       (.setDefaultLineWidth ~drawer (float old-line-width#)))))

(defn ellipse [^ShapeDrawer drawer [x y] radius-x radius-y color]
  (.setColor drawer ^Color color)
  (.ellipse drawer (float x) (float y) (float radius-x) (float radius-y)))

(defn filled-ellipse [^ShapeDrawer drawer [x y] radius-x radius-y color]
  (.setColor drawer ^Color color)
  (.filledEllipse drawer (float x) (float y) (float radius-x) (float radius-y)))

(defn circle [^ShapeDrawer drawer [x y] radius color]
  (.setColor drawer ^Color color)
  (.circle drawer (float x) (float y) (float radius)))

(defn filled-circle [^ShapeDrawer drawer [x y] radius color]
  (.setColor drawer ^Color color)
  (.filledCircle drawer (float x) (float y) (float radius)))

(defn- degree->radians [degree] ; TODO not here
  (* degree (/ (Math/PI) 180)))

(defn arc [^ShapeDrawer drawer [centre-x centre-y] radius start-angle degree color]
  (.setColor drawer ^Color color)
  (.arc drawer centre-x centre-y radius start-angle (degree->radians degree)))

(defn sector [^ShapeDrawer drawer [centre-x centre-y] radius start-angle degree color]
  (.setColor drawer ^Color color)
  (.sector drawer centre-x centre-y radius start-angle (degree->radians degree)))

(defn rectangle [^ShapeDrawer drawer x y w h color]
  (.setColor drawer ^Color color)
  (.rectangle drawer x y w h))

(defn filled-rectangle [^ShapeDrawer drawer x y w h color]
  (.setColor drawer ^Color color)
  (.filledRectangle drawer (float x) (float y) (float w) (float h)))

(defn line
  ([^ShapeDrawer drawer [x y] [ex ey] color]
   (line drawer x y ex ey color))
  ([^ShapeDrawer drawer x y ex ey color]
   (.setColor drawer ^Color color)
   (.line drawer (float x) (float y) (float ex) (float ey))))

(defn grid
  [drawer leftx bottomy gridw gridh cellw cellh color]
  (let [w (* gridw cellw)
        h (* gridh cellh)
        topy (+ bottomy h)
        rightx (+ leftx w)]
    (doseq [idx (range (inc gridw))
            :let [linex (+ leftx (* idx cellw))]]
           (line drawer linex topy linex bottomy color))
    (doseq [idx (range (inc gridh))
            :let [liney (+ bottomy (* idx cellh))]]
           (line drawer leftx liney rightx liney color))))
