all: latest 8.13 8.12

%:      IMAGE=ysli/sfdev:$@
%:      DOCKERFILE=Dockerfile.$@
latest: DOCKERFILE=Dockerfile

%:
	docker build -t $(IMAGE) -f $(DOCKERFILE) .
	docker push $(IMAGE)
