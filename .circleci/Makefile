all: 8.15 dev

%:      IMAGE=ysli/sfdev:$@
%:      DOCKERFILE=Dockerfile.$@

%:
	docker build -t $(IMAGE) -f $(DOCKERFILE) .
	docker push $(IMAGE)
