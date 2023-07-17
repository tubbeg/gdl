(ns ^:no-doc gdx.utils)

(defn set-var-root [v value]
  (alter-var-root v (constantly value)))

