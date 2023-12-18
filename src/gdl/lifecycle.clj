(ns gdl.lifecycle)

(defprotocol Disposable
  (dispose [_]))

(defprotocol Screen
  (show   [_ context])
  (hide   [_ context])
  (render [_ context])
  (tick   [_ context delta]))
