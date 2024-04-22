all: 8.17 8.18 8.19 dev

%:      IMAGE=ysli/sfdev:$@
%:      DOCKERFILE=Dockerfile.$@

%:
	docker build -t $(IMAGE) -f $(DOCKERFILE) .
	docker push $(IMAGE)
