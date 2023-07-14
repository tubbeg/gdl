(declare ^:no-doc shape-drawer)

(let [shape-drawer-texture (atom nil)]

  (app/on-create
   (let [pixmap (doto (Pixmap. 1 1 Pixmap$Format/RGBA8888)
                  (.setColor Color/WHITE)
                  (.drawPixel 0 0))
         texture (Texture. pixmap)
         _ (.dispose pixmap)
         region (TextureRegion. texture 0 0 1 1)]
     (reset! shape-drawer-texture texture)
     (set-var-root #'shape-drawer (shape-drawer/shape-drawer batch region))))

  (app/on-destroy
   (.dispose ^Texture @shape-drawer-texture)))

(defn- set-shapes-color [color]
  (shape-drawer/set-color shape-drawer color))

(defn ^:no-doc set-default-line-width [width]
  (shape-drawer/set-default-line-width shape-drawer width))

(defn ^:no-doc set-shape-drawer-unit-scale []
  (set-default-line-width *unit-scale*))

(defmacro with-shape-drawer-line-width [width & exprs]
  `(let [old-line-width# (shape-drawer/get-default-line-width shape-drawer)]
     (set-default-line-width (* ~width old-line-width#))
     ~@exprs
     (set-default-line-width old-line-width#)))

(defn draw-ellipse [[x y] radius-x radius-y color]
  (set-shapes-color color)
  (shape-drawer/ellipse shape-drawer x y radius-x radius-y))

(defn fill-ellipse [[x y] radius-x radius-y color]
  (set-shapes-color color)
  (shape-drawer/filled-ellipse shape-drawer x y radius-x radius-y))

(defn draw-circle [[x y] radius color]
  (set-shapes-color color)
  (shape-drawer/circle shape-drawer x y radius))

(defn fill-circle [[x y] radius color]
  (set-shapes-color color)
  (shape-drawer/filled-circle shape-drawer x y radius))

(defn- degree->radians [degree]
  (* degree (/ (Math/PI) 180)))

(defn draw-arc [[centre-x centre-y] radius start-angle degree color]
  (set-shapes-color color)
  (shape-drawer/arc shape-drawer centre-x centre-y radius start-angle (degree->radians degree)))

(defn draw-sector [[centre-x centre-y] radius start-angle degree color]
  (set-shapes-color color)
  (shape-drawer/sector shape-drawer centre-x centre-y radius start-angle (degree->radians degree)))

(defn draw-rect
  ([[x y w h] color]
   (draw-rect x y w h color))
  ([x y w h color]
   (set-shapes-color color)
   (shape-drawer/rectangle shape-drawer x y w h)))

(defn fill-rect
  ([[x y w h] color]
   (fill-rect x y w h color))
  ([x y w h color]
   (set-shapes-color color)
   (shape-drawer/filled-rectangle shape-drawer x y w h)))

(defn draw-line
  ([[x y] [ex ey] color]
   (draw-line x y ex ey color))
  ([x y ex ey color]
   (set-shapes-color color)
   (shape-drawer/line shape-drawer x y ex ey)))

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
